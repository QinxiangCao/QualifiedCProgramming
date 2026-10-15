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
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import AUXLib.MonotonicList.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P051_986A_fair_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_proof.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_char_strategy_goal.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_char_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_ext_strategy_goal.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_ext_strategy_proof.

(*----- Function bfs_type -----*)

Definition bfs_type_safety_wit_1 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (dist_before: (@list Z)) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (0 <= m)) (PreH4 : (m <= 100000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 100)) (PreH7 : (n_pre = (Zlength (goods)))) (PreH8 : (m = (Zlength (edges)))) (PreH9 : (AdjBuild n_pre m edges hd nx tlst )) (PreH10 : (NxtRange m nx )) (PreH11 : (ArcToRange n_pre m tlst )) (PreH12 : ((Zlength (dist_before)) = 100005)) ,
  ((( &( "v" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full dist_pre 100005 dist_before )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bfs_type_safety_wit_2 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= v)) (PreH14 : (v <= (n_pre + 1 ))) (PreH15 : ((Zlength (dl)) = 100005)) (PreH16 : forall (w: Z) , (((1 <= w) /\ (w < v)) -> ((Znth (w) (dl) (0)) = (-1)))) ,
  (IntArray.full dist_pre 100005 (replace_Znth (v) ((-1)) (dl)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition bfs_type_safety_wit_3 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= v)) (PreH14 : (v <= (n_pre + 1 ))) (PreH15 : ((Zlength (dl)) = 100005)) (PreH16 : forall (w: Z) , (((1 <= w) /\ (w < v)) -> ((Znth (w) (dl) (0)) = (-1)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full dist_pre 100005 dl )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition bfs_type_safety_wit_4 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= v)) (PreH14 : (v <= (n_pre + 1 ))) (PreH15 : ((Zlength (dl)) = 100005)) (PreH16 : forall (w: Z) , (((1 <= w) /\ (w < v)) -> ((Znth (w) (dl) (0)) = (-1)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full dist_pre 100005 dl )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bfs_type_safety_wit_5 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= v)) (PreH14 : (v <= (n_pre + 1 ))) (PreH15 : ((Zlength (dl)) = 100005)) (PreH16 : forall (w: Z) , (((1 <= w) /\ (w < v)) -> ((Znth (w) (dl) (0)) = (-1)))) ,
  ((( &( "qt" ) )) # Int  |->_)
  **  ((( &( "qh" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full dist_pre 100005 dl )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition bfs_type_safety_wit_6 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= v)) (PreH14 : (v <= (n_pre + 1 ))) (PreH15 : ((Zlength (dl)) = 100005)) (PreH16 : forall (w: Z) , (((1 <= w) /\ (w < v)) -> ((Znth (w) (dl) (0)) = (-1)))) ,
  ((( &( "qh" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full dist_pre 100005 dl )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition bfs_type_safety_wit_7 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= v)) (PreH14 : (v <= (n_pre + 1 ))) (PreH15 : ((Zlength (dl)) = 100005)) (PreH16 : forall (w: Z) , (((1 <= w) /\ (w < v)) -> ((Znth (w) (dl) (0)) = (-1)))) ,
  ((( &( "v" ) )) # Int  |->_)
  **  ((( &( "qt" ) )) # Int  |-> 0)
  **  ((( &( "qh" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full dist_pre 100005 dl )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bfs_type_safety_wit_8 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : ((Znth (v - 1 ) goods 0) = c_pre)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= v)) (PreH15 : (v <= (n_pre + 1 ))) (PreH16 : (qh = 0)) (PreH17 : (0 <= qt)) (PreH18 : (qt = (Zlength (Q)))) (PreH19 : (qt <= (v - 1 ))) (PreH20 : ((Zlength (dl)) = 100005)) (PreH21 : (BfsInit n_pre goods c_pre Q dl v )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "qh" ) )) # Int  |-> qh)
  **  ((( &( "qt" ) )) # Int  |-> qt)
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition bfs_type_safety_wit_9 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : ((Znth (v - 1 ) goods 0) = c_pre)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= v)) (PreH15 : (v <= (n_pre + 1 ))) (PreH16 : (qh = 0)) (PreH17 : (0 <= qt)) (PreH18 : (qt = (Zlength (Q)))) (PreH19 : (qt <= (v - 1 ))) (PreH20 : ((Zlength (dl)) = 100005)) (PreH21 : (BfsInit n_pre goods c_pre Q dl v )) ,
  (IntArray.seg ( &( "queue_" ) ) 0 (qt + 1 ) (app (Q) ((cons (v) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "queue_" ) ) (qt + 1 ) n_pre )
  **  (IntArray.full dist_pre 100005 (replace_Znth (v) (0) (dl)) )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "qh" ) )) # Int  |-> qh)
  **  ((( &( "qt" ) )) # Int  |-> qt)
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
|--
  “ ((qt + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (qt + 1 )) ”
.

Definition bfs_type_safety_wit_10 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : ((Znth (v - 1 ) goods 0) = c_pre)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= v)) (PreH15 : (v <= (n_pre + 1 ))) (PreH16 : (qh = 0)) (PreH17 : (0 <= qt)) (PreH18 : (qt = (Zlength (Q)))) (PreH19 : (qt <= (v - 1 ))) (PreH20 : ((Zlength (dl)) = 100005)) (PreH21 : (BfsInit n_pre goods c_pre Q dl v )) ,
  (IntArray.seg ( &( "queue_" ) ) 0 (qt + 1 ) (app (Q) ((cons (v) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "queue_" ) ) (qt + 1 ) n_pre )
  **  (IntArray.full dist_pre 100005 (replace_Znth (v) (0) (dl)) )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "qh" ) )) # Int  |-> qh)
  **  ((( &( "qt" ) )) # Int  |-> qt)
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bfs_type_safety_wit_11 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : ((Znth (v - 1 ) goods 0) = c_pre)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= v)) (PreH15 : (v <= (n_pre + 1 ))) (PreH16 : (qh = 0)) (PreH17 : (0 <= qt)) (PreH18 : (qt = (Zlength (Q)))) (PreH19 : (qt <= (v - 1 ))) (PreH20 : ((Zlength (dl)) = 100005)) (PreH21 : (BfsInit n_pre goods c_pre Q dl v )) ,
  (IntArray.seg ( &( "queue_" ) ) 0 (qt + 1 ) (app (Q) ((cons (v) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "queue_" ) ) (qt + 1 ) n_pre )
  **  (IntArray.full dist_pre 100005 (replace_Znth (v) (0) (dl)) )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "qh" ) )) # Int  |-> qh)
  **  ((( &( "qt" ) )) # Int  |-> (qt + 1 ))
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition bfs_type_safety_wit_12 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : ((Znth (v - 1 ) goods 0) <> c_pre)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= v)) (PreH15 : (v <= (n_pre + 1 ))) (PreH16 : (qh = 0)) (PreH17 : (0 <= qt)) (PreH18 : (qt = (Zlength (Q)))) (PreH19 : (qt <= (v - 1 ))) (PreH20 : ((Zlength (dl)) = 100005)) (PreH21 : (BfsInit n_pre goods c_pre Q dl v )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "qh" ) )) # Int  |-> qh)
  **  ((( &( "qt" ) )) # Int  |-> qt)
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition bfs_type_safety_wit_13 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (qh < qt)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (0 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q)))) (PreH16 : (qt <= n_pre)) (PreH17 : ((Zlength (dl)) = 100005)) (PreH18 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH19 : (BfsExpanded n_pre edges Q dl qh )) (PreH20 : ((qh < qt) -> (BfsBounded Q dl ((Znth ((Znth (qh) (Q) (0))) (dl) (0)) + 1 ) ))) ,
  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  ((( &( "u" ) )) # Int  |-> (Znth (qh - 0 ) Q 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "qh" ) )) # Int  |-> qh)
  **  ((( &( "qt" ) )) # Int  |-> qt)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
|--
  “ ((qh + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (qh + 1 )) ”
.

Definition bfs_type_safety_wit_14 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (qh < qt)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (0 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q)))) (PreH16 : (qt <= n_pre)) (PreH17 : ((Zlength (dl)) = 100005)) (PreH18 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH19 : (BfsExpanded n_pre edges Q dl qh )) (PreH20 : ((qh < qt) -> (BfsBounded Q dl ((Znth ((Znth (qh) (Q) (0))) (dl) (0)) + 1 ) ))) ,
  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  ((( &( "u" ) )) # Int  |-> (Znth (qh - 0 ) Q 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "qh" ) )) # Int  |-> qh)
  **  ((( &( "qt" ) )) # Int  |-> qt)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bfs_type_safety_wit_15 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl: (@list Z)) (u: Z) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (0 <= m)) (PreH4 : (m <= 100000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 100)) (PreH7 : (n_pre = (Zlength (goods)))) (PreH8 : (m = (Zlength (edges)))) (PreH9 : (AdjBuild n_pre m edges hd nx tlst )) (PreH10 : (NxtRange m nx )) (PreH11 : (ArcToRange n_pre m tlst )) (PreH12 : (1 <= qh)) (PreH13 : (qh <= qt)) (PreH14 : (qt = (Zlength (Q)))) (PreH15 : (qt <= n_pre)) (PreH16 : (u = (Znth ((qh - 1 )) (Q) (0)))) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : (0 <= (Znth (u) (dl) (0)))) (PreH20 : ((Znth (u) (dl) (0)) <= (n_pre - 1 ))) (PreH21 : ((-1) <= e)) (PreH22 : (e < (2 * m ))) (PreH23 : ((Zlength (dl)) = 100005)) (PreH24 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH25 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre))) (PreH26 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH27 : (BfsExpanded n_pre edges Q dl (qh - 1 ) )) (PreH28 : (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) )) (PreH29 : (BfsScan m edges nx tlst Q dl u e )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "qh" ) )) # Int  |-> qh)
  **  ((( &( "qt" ) )) # Int  |-> qt)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition bfs_type_safety_wit_16 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl: (@list Z)) (u: Z) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (0 <= m)) (PreH4 : (m <= 100000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 100)) (PreH7 : (n_pre = (Zlength (goods)))) (PreH8 : (m = (Zlength (edges)))) (PreH9 : (AdjBuild n_pre m edges hd nx tlst )) (PreH10 : (NxtRange m nx )) (PreH11 : (ArcToRange n_pre m tlst )) (PreH12 : (1 <= qh)) (PreH13 : (qh <= qt)) (PreH14 : (qt = (Zlength (Q)))) (PreH15 : (qt <= n_pre)) (PreH16 : (u = (Znth ((qh - 1 )) (Q) (0)))) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : (0 <= (Znth (u) (dl) (0)))) (PreH20 : ((Znth (u) (dl) (0)) <= (n_pre - 1 ))) (PreH21 : ((-1) <= e)) (PreH22 : (e < (2 * m ))) (PreH23 : ((Zlength (dl)) = 100005)) (PreH24 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH25 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre))) (PreH26 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH27 : (BfsExpanded n_pre edges Q dl (qh - 1 ) )) (PreH28 : (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) )) (PreH29 : (BfsScan m edges nx tlst Q dl u e )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "qh" ) )) # Int  |-> qh)
  **  ((( &( "qt" ) )) # Int  |-> qt)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bfs_type_safety_wit_17 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl: (@list Z)) (u: Z) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (e <> (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q)))) (PreH16 : (qt <= n_pre)) (PreH17 : (u = (Znth ((qh - 1 )) (Q) (0)))) (PreH18 : (1 <= u)) (PreH19 : (u <= n_pre)) (PreH20 : (0 <= (Znth (u) (dl) (0)))) (PreH21 : ((Znth (u) (dl) (0)) <= (n_pre - 1 ))) (PreH22 : ((-1) <= e)) (PreH23 : (e < (2 * m ))) (PreH24 : ((Zlength (dl)) = 100005)) (PreH25 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH26 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre))) (PreH27 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH28 : (BfsExpanded n_pre edges Q dl (qh - 1 ) )) (PreH29 : (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) )) (PreH30 : (BfsScan m edges nx tlst Q dl u e )) ,
  (IntArray.full dist_pre 100005 dl )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  ((( &( "v" ) )) # Int  |-> (Znth e tlst 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "qh" ) )) # Int  |-> qh)
  **  ((( &( "qt" ) )) # Int  |-> qt)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition bfs_type_safety_wit_18 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl: (@list Z)) (u: Z) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl) (0)))) (PreH22 : ((Znth (u) (dl) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH29 : (BfsExpanded n_pre edges Q dl (qh - 1 ) )) (PreH30 : (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q dl u e )) ,
  (IntArray.full dist_pre 100005 dl )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  ((( &( "v" ) )) # Int  |-> (Znth e tlst 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "qh" ) )) # Int  |-> qh)
  **  ((( &( "qt" ) )) # Int  |-> qt)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
|--
  “ (((Znth u dl 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth u dl 0) + 1 )) ”
.

Definition bfs_type_safety_wit_19 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl: (@list Z)) (u: Z) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl) (0)))) (PreH22 : ((Znth (u) (dl) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH29 : (BfsExpanded n_pre edges Q dl (qh - 1 ) )) (PreH30 : (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q dl u e )) ,
  (IntArray.full dist_pre 100005 dl )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  ((( &( "v" ) )) # Int  |-> (Znth e tlst 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "qh" ) )) # Int  |-> qh)
  **  ((( &( "qt" ) )) # Int  |-> qt)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bfs_type_safety_wit_20 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl: (@list Z)) (u: Z) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl) (0)))) (PreH22 : ((Znth (u) (dl) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH29 : (BfsExpanded n_pre edges Q dl (qh - 1 ) )) (PreH30 : (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q dl u e )) ,
  (IntArray.seg ( &( "queue_" ) ) 0 (qt + 1 ) (app (Q) ((cons ((Znth e tlst 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "queue_" ) ) (qt + 1 ) n_pre )
  **  (IntArray.full dist_pre 100005 (replace_Znth ((Znth e tlst 0)) (((Znth u dl 0) + 1 )) (dl)) )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  ((( &( "v" ) )) # Int  |-> (Znth e tlst 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "qh" ) )) # Int  |-> qh)
  **  ((( &( "qt" ) )) # Int  |-> qt)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
|--
  “ ((qt + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (qt + 1 )) ”
.

Definition bfs_type_safety_wit_21 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl: (@list Z)) (u: Z) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl) (0)))) (PreH22 : ((Znth (u) (dl) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH29 : (BfsExpanded n_pre edges Q dl (qh - 1 ) )) (PreH30 : (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q dl u e )) ,
  (IntArray.seg ( &( "queue_" ) ) 0 (qt + 1 ) (app (Q) ((cons ((Znth e tlst 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "queue_" ) ) (qt + 1 ) n_pre )
  **  (IntArray.full dist_pre 100005 (replace_Znth ((Znth e tlst 0)) (((Znth u dl 0) + 1 )) (dl)) )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  ((( &( "v" ) )) # Int  |-> (Znth e tlst 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "dist" ) )) # Ptr  |-> dist_pre)
  **  ((( &( "qh" ) )) # Int  |-> qh)
  **  ((( &( "qt" ) )) # Int  |-> qt)
  **  ((( &( "u" ) )) # Int  |-> u)
  **  ((( &( "e" ) )) # Int  |-> e)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition bfs_type_entail_wit_1 := 
(
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (dist_before: (@list Z)) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (0 <= m)) (PreH4 : (m <= 100000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 100)) (PreH7 : (n_pre = (Zlength (goods)))) (PreH8 : (m = (Zlength (edges)))) (PreH9 : (AdjBuild n_pre m edges hd nx tlst )) (PreH10 : (NxtRange m nx )) (PreH11 : (ArcToRange n_pre m tlst )) (PreH12 : ((Zlength (dist_before)) = 100005)) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full dist_pre 100005 dist_before )
|--
  EX (dl: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ forall (w: Z) , (((1 <= w) /\ (w < 1)) -> ((Znth (w) (dl) (0)) = (-1))) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full dist_pre 100005 dl )
) \/
(
forall (c_pre: Z) (n_pre: Z) (dist_before: (@list Z)) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (0 <= m)) (PreH4 : (m <= 100000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 100)) (PreH7 : (n_pre = (Zlength (goods)))) (PreH8 : (m = (Zlength (edges)))) (PreH9 : (AdjBuild n_pre m edges hd nx tlst )) (PreH10 : (NxtRange m nx )) (PreH11 : (ArcToRange n_pre m tlst )) (PreH12 : ((Zlength (dist_before)) = 100005)) ,
  TT && emp 
|--
  “ forall (w: Z) , (((1 <= w) /\ (w < 1)) -> ((Znth (w) (dist_before) (0)) = (-1))) ”
  &&  emp
).

Definition bfs_type_entail_wit_1_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (dist_before: (@list Z)) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (0 <= m)) (PreH4 : (m <= 100000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 100)) (PreH7 : (n_pre = (Zlength (goods)))) (PreH8 : (m = (Zlength (edges)))) (PreH9 : (AdjBuild n_pre m edges hd nx tlst )) (PreH10 : (NxtRange m nx )) (PreH11 : (ArcToRange n_pre m tlst )) (PreH12 : ((Zlength (dist_before)) = 100005)) ,
  forall (w: Z) , (((1 <= w) /\ (w < 1)) -> ((Znth (w) (dist_before) (0)) = (-1)))
.

Definition bfs_type_entail_wit_2 := 
(
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= v)) (PreH14 : (v <= (n_pre + 1 ))) (PreH15 : ((Zlength (dl_2)) = 100005)) (PreH16 : forall (w: Z) , (((1 <= w) /\ (w < v)) -> ((Znth (w) (dl_2) (0)) = (-1)))) ,
  (IntArray.full dist_pre 100005 (replace_Znth (v) ((-1)) (dl_2)) )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
|--
  EX (dl: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ forall (w: Z) , (((1 <= w) /\ (w < (v + 1 ))) -> ((Znth (w) (dl) (0)) = (-1))) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full dist_pre 100005 dl )
) \/
(
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= v)) (PreH14 : (v <= (n_pre + 1 ))) (PreH15 : ((Zlength (dl_2)) = 100005)) (PreH16 : forall (w: Z) , (((1 <= w) /\ (w < v)) -> ((Znth (w) (dl_2) (0)) = (-1)))) ,
  TT && emp 
|--
  “ ((Zlength ((replace_Znth (v) ((-1)) (dl_2)))) = 100005) ”
  &&  emp
).

Definition bfs_type_entail_wit_2_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= v)) (PreH14 : (v <= (n_pre + 1 ))) (PreH15 : ((Zlength (dl_2)) = 100005)) (PreH16 : forall (w: Z) , (((1 <= w) /\ (w < v)) -> ((Znth (w) (dl_2) (0)) = (-1)))) ,
  ((Zlength ((replace_Znth (v) ((-1)) (dl_2)))) = 100005)
.

Definition bfs_type_entail_wit_3 := 
(
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= v)) (PreH14 : (v <= (n_pre + 1 ))) (PreH15 : ((Zlength (dl_2)) = 100005)) (PreH16 : forall (w: Z) , (((1 <= w) /\ (w < v)) -> ((Znth (w) (dl_2) (0)) = (-1)))) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full dist_pre 100005 dl_2 )
|--
  EX (dl: (@list Z))  (Q: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (Zlength (Q))) ” 
  &&  “ (0 <= (1 - 1 )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ (BfsInit n_pre goods c_pre Q dl 1 ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 0 Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) 0 n_pre )
  **  (IntArray.full dist_pre 100005 dl )
) \/
(
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= v)) (PreH14 : (v <= (n_pre + 1 ))) (PreH15 : ((Zlength (dl_2)) = 100005)) (PreH16 : forall (w: Z) , (((1 <= w) /\ (w < v)) -> ((Znth (w) (dl_2) (0)) = (-1)))) ,
  TT && emp 
|--
  “ (BfsInit n_pre goods c_pre (@nil Z) dl_2 1 ) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ”
  &&  emp
).

Definition bfs_type_entail_wit_3_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= v)) (PreH14 : (v <= (n_pre + 1 ))) (PreH15 : ((Zlength (dl_2)) = 100005)) (PreH16 : forall (w: Z) , (((1 <= w) /\ (w < v)) -> ((Znth (w) (dl_2) (0)) = (-1)))) ,
  (BfsInit n_pre goods c_pre (@nil Z) dl_2 1 )
.

Definition bfs_type_entail_wit_3_split_goal_2 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= v)) (PreH14 : (v <= (n_pre + 1 ))) (PreH15 : ((Zlength (dl_2)) = 100005)) (PreH16 : forall (w: Z) , (((1 <= w) /\ (w < v)) -> ((Znth (w) (dl_2) (0)) = (-1)))) ,
  (0 = (Zlength ((@nil Z))))
.

Definition bfs_type_entail_wit_4_1 := 
(
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q_2: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : ((Znth (v - 1 ) goods 0) = c_pre)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= v)) (PreH15 : (v <= (n_pre + 1 ))) (PreH16 : (qh = 0)) (PreH17 : (0 <= qt)) (PreH18 : (qt = (Zlength (Q_2)))) (PreH19 : (qt <= (v - 1 ))) (PreH20 : ((Zlength (dl_2)) = 100005)) (PreH21 : (BfsInit n_pre goods c_pre Q_2 dl_2 v )) ,
  (IntArray.seg ( &( "queue_" ) ) 0 (qt + 1 ) (app (Q_2) ((cons (v) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "queue_" ) ) (qt + 1 ) n_pre )
  **  (IntArray.full dist_pre 100005 (replace_Znth (v) (0) (dl_2)) )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
|--
  EX (dl: (@list Z))  (Q: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (qh = 0) ” 
  &&  “ (0 <= (qt + 1 )) ” 
  &&  “ ((qt + 1 ) = (Zlength (Q))) ” 
  &&  “ ((qt + 1 ) <= ((v + 1 ) - 1 )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ (BfsInit n_pre goods c_pre Q dl (v + 1 ) ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 (qt + 1 ) Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) (qt + 1 ) n_pre )
  **  (IntArray.full dist_pre 100005 dl )
) \/
(
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q_2: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : ((Znth (v - 1 ) goods 0) = c_pre)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= v)) (PreH15 : (v <= (n_pre + 1 ))) (PreH16 : (qh = 0)) (PreH17 : (0 <= qt)) (PreH18 : (qt = (Zlength (Q_2)))) (PreH19 : (qt <= (v - 1 ))) (PreH20 : ((Zlength (dl_2)) = 100005)) (PreH21 : (BfsInit n_pre goods c_pre Q_2 dl_2 v )) ,
  TT && emp 
|--
  “ (BfsInit n_pre goods c_pre (app (Q_2) ((cons (v) ((@nil Z))))) (replace_Znth (v) (0) (dl_2)) (v + 1 ) ) ” 
  &&  “ ((Zlength ((replace_Znth (v) (0) (dl_2)))) = 100005) ” 
  &&  “ ((qt + 1 ) = (Zlength ((app (Q_2) ((cons (v) ((@nil Z)))))))) ”
  &&  emp
).

Definition bfs_type_entail_wit_4_1_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q_2: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : ((Znth (v - 1 ) goods 0) = c_pre)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= v)) (PreH15 : (v <= (n_pre + 1 ))) (PreH16 : (qh = 0)) (PreH17 : (0 <= qt)) (PreH18 : (qt = (Zlength (Q_2)))) (PreH19 : (qt <= (v - 1 ))) (PreH20 : ((Zlength (dl_2)) = 100005)) (PreH21 : (BfsInit n_pre goods c_pre Q_2 dl_2 v )) ,
  (BfsInit n_pre goods c_pre (app (Q_2) ((cons (v) ((@nil Z))))) (replace_Znth (v) (0) (dl_2)) (v + 1 ) )
.

Definition bfs_type_entail_wit_4_1_split_goal_2 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q_2: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : ((Znth (v - 1 ) goods 0) = c_pre)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= v)) (PreH15 : (v <= (n_pre + 1 ))) (PreH16 : (qh = 0)) (PreH17 : (0 <= qt)) (PreH18 : (qt = (Zlength (Q_2)))) (PreH19 : (qt <= (v - 1 ))) (PreH20 : ((Zlength (dl_2)) = 100005)) (PreH21 : (BfsInit n_pre goods c_pre Q_2 dl_2 v )) ,
  ((Zlength ((replace_Znth (v) (0) (dl_2)))) = 100005)
.

Definition bfs_type_entail_wit_4_1_split_goal_3 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q_2: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : ((Znth (v - 1 ) goods 0) = c_pre)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= v)) (PreH15 : (v <= (n_pre + 1 ))) (PreH16 : (qh = 0)) (PreH17 : (0 <= qt)) (PreH18 : (qt = (Zlength (Q_2)))) (PreH19 : (qt <= (v - 1 ))) (PreH20 : ((Zlength (dl_2)) = 100005)) (PreH21 : (BfsInit n_pre goods c_pre Q_2 dl_2 v )) ,
  ((qt + 1 ) = (Zlength ((app (Q_2) ((cons (v) ((@nil Z))))))))
.

Definition bfs_type_entail_wit_4_2 := 
(
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q_2: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : ((Znth (v - 1 ) goods 0) <> c_pre)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= v)) (PreH15 : (v <= (n_pre + 1 ))) (PreH16 : (qh = 0)) (PreH17 : (0 <= qt)) (PreH18 : (qt = (Zlength (Q_2)))) (PreH19 : (qt <= (v - 1 ))) (PreH20 : ((Zlength (dl_2)) = 100005)) (PreH21 : (BfsInit n_pre goods c_pre Q_2 dl_2 v )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q_2 )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl_2 )
|--
  EX (dl: (@list Z))  (Q: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (qh = 0) ” 
  &&  “ (0 <= qt) ” 
  &&  “ (qt = (Zlength (Q))) ” 
  &&  “ (qt <= ((v + 1 ) - 1 )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ (BfsInit n_pre goods c_pre Q dl (v + 1 ) ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
) \/
(
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q_2: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : ((Znth (v - 1 ) goods 0) <> c_pre)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= v)) (PreH15 : (v <= (n_pre + 1 ))) (PreH16 : (qh = 0)) (PreH17 : (0 <= qt)) (PreH18 : (qt = (Zlength (Q_2)))) (PreH19 : (qt <= (v - 1 ))) (PreH20 : ((Zlength (dl_2)) = 100005)) (PreH21 : (BfsInit n_pre goods c_pre Q_2 dl_2 v )) ,
  TT && emp 
|--
  “ (BfsInit n_pre goods c_pre Q_2 dl_2 (v + 1 ) ) ”
  &&  emp
).

Definition bfs_type_entail_wit_4_2_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q_2: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : ((Znth (v - 1 ) goods 0) <> c_pre)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= v)) (PreH15 : (v <= (n_pre + 1 ))) (PreH16 : (qh = 0)) (PreH17 : (0 <= qt)) (PreH18 : (qt = (Zlength (Q_2)))) (PreH19 : (qt <= (v - 1 ))) (PreH20 : ((Zlength (dl_2)) = 100005)) (PreH21 : (BfsInit n_pre goods c_pre Q_2 dl_2 v )) ,
  (BfsInit n_pre goods c_pre Q_2 dl_2 (v + 1 ) )
.

Definition bfs_type_entail_wit_5 := 
(
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q_2: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= v)) (PreH14 : (v <= (n_pre + 1 ))) (PreH15 : (qh = 0)) (PreH16 : (0 <= qt)) (PreH17 : (qt = (Zlength (Q_2)))) (PreH18 : (qt <= (v - 1 ))) (PreH19 : ((Zlength (dl_2)) = 100005)) (PreH20 : (BfsInit n_pre goods c_pre Q_2 dl_2 v )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q_2 )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl_2 )
|--
  EX (dl: (@list Z))  (Q: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (0 <= qh) ” 
  &&  “ (qh <= qt) ” 
  &&  “ (qt = (Zlength (Q))) ” 
  &&  “ (qt <= n_pre) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ (BfsCore n_pre edges goods c_pre Q dl ) ” 
  &&  “ (BfsExpanded n_pre edges Q dl qh ) ” 
  &&  “ ((qh < qt) -> (BfsBounded Q dl ((Znth ((Znth (qh) (Q) (0))) (dl) (0)) + 1 ) )) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
) \/
(
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q_2: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= v)) (PreH14 : (v <= (n_pre + 1 ))) (PreH15 : (qh = 0)) (PreH16 : (0 <= qt)) (PreH17 : (qt = (Zlength (Q_2)))) (PreH18 : (qt <= (v - 1 ))) (PreH19 : ((Zlength (dl_2)) = 100005)) (PreH20 : (BfsInit n_pre goods c_pre Q_2 dl_2 v )) ,
  TT && emp 
|--
  “ ((0 < qt) -> (BfsBounded Q_2 dl_2 ((Znth ((Znth (0) (Q_2) (0))) (dl_2) (0)) + 1 ) )) ” 
  &&  “ (BfsExpanded n_pre edges Q_2 dl_2 0 ) ” 
  &&  “ (BfsCore n_pre edges goods c_pre Q_2 dl_2 ) ”
  &&  emp
).

Definition bfs_type_entail_wit_5_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q_2: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= v)) (PreH14 : (v <= (n_pre + 1 ))) (PreH15 : (qh = 0)) (PreH16 : (0 <= qt)) (PreH17 : (qt = (Zlength (Q_2)))) (PreH18 : (qt <= (v - 1 ))) (PreH19 : ((Zlength (dl_2)) = 100005)) (PreH20 : (BfsInit n_pre goods c_pre Q_2 dl_2 v )) ,
  ((0 < qt) -> (BfsBounded Q_2 dl_2 ((Znth ((Znth (0) (Q_2) (0))) (dl_2) (0)) + 1 ) ))
.

Definition bfs_type_entail_wit_5_split_goal_2 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q_2: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= v)) (PreH14 : (v <= (n_pre + 1 ))) (PreH15 : (qh = 0)) (PreH16 : (0 <= qt)) (PreH17 : (qt = (Zlength (Q_2)))) (PreH18 : (qt <= (v - 1 ))) (PreH19 : ((Zlength (dl_2)) = 100005)) (PreH20 : (BfsInit n_pre goods c_pre Q_2 dl_2 v )) ,
  (BfsExpanded n_pre edges Q_2 dl_2 0 )
.

Definition bfs_type_entail_wit_5_split_goal_3 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q_2: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= v)) (PreH14 : (v <= (n_pre + 1 ))) (PreH15 : (qh = 0)) (PreH16 : (0 <= qt)) (PreH17 : (qt = (Zlength (Q_2)))) (PreH18 : (qt <= (v - 1 ))) (PreH19 : ((Zlength (dl_2)) = 100005)) (PreH20 : (BfsInit n_pre goods c_pre Q_2 dl_2 v )) ,
  (BfsCore n_pre edges goods c_pre Q_2 dl_2 )
.

Definition bfs_type_entail_wit_6 := 
(
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (qh < qt)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (0 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q)))) (PreH16 : (qt <= n_pre)) (PreH17 : ((Zlength (dl_2)) = 100005)) (PreH18 : (BfsCore n_pre edges goods c_pre Q dl_2 )) (PreH19 : (BfsExpanded n_pre edges Q dl_2 qh )) (PreH20 : ((qh < qt) -> (BfsBounded Q dl_2 ((Znth ((Znth (qh) (Q) (0))) (dl_2) (0)) + 1 ) ))) ,
  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl_2 )
|--
  EX (dl: (@list Z))  (Q_2: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= (qh + 1 )) ” 
  &&  “ ((qh + 1 ) <= qt) ” 
  &&  “ (qt = (Zlength (Q_2))) ” 
  &&  “ (qt <= n_pre) ” 
  &&  “ ((Znth (qh - 0 ) Q 0) = (Znth (((qh + 1 ) - 1 )) (Q_2) (0))) ” 
  &&  “ (1 <= (Znth (qh - 0 ) Q 0)) ” 
  &&  “ ((Znth (qh - 0 ) Q 0) <= n_pre) ” 
  &&  “ (0 <= (Znth ((Znth (qh - 0 ) Q 0)) (dl) (0))) ” 
  &&  “ ((Znth ((Znth (qh - 0 ) Q 0)) (dl) (0)) <= (n_pre - 1 )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ (BfsCore n_pre edges goods c_pre Q_2 dl ) ” 
  &&  “ (BfsExpanded n_pre edges Q_2 dl ((qh + 1 ) - 1 ) ) ” 
  &&  “ (BfsBounded Q_2 dl ((Znth ((Znth (qh - 0 ) Q 0)) (dl) (0)) + 1 ) ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q_2 )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
) \/
(
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (qh < qt)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (0 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q)))) (PreH16 : (qt <= n_pre)) (PreH17 : ((Zlength (dl_2)) = 100005)) (PreH18 : (BfsCore n_pre edges goods c_pre Q dl_2 )) (PreH19 : (BfsExpanded n_pre edges Q dl_2 qh )) (PreH20 : ((qh < qt) -> (BfsBounded Q dl_2 ((Znth ((Znth (qh) (Q) (0))) (dl_2) (0)) + 1 ) ))) ,
  TT && emp 
|--
  “ (BfsBounded Q dl_2 ((Znth ((Znth (qh - 0 ) Q 0)) (dl_2) (0)) + 1 ) ) ” 
  &&  “ (BfsExpanded n_pre edges Q dl_2 ((qh + 1 ) - 1 ) ) ” 
  &&  “ ((Znth ((Znth (qh - 0 ) Q 0)) (dl_2) (0)) <= (n_pre - 1 )) ” 
  &&  “ (0 <= (Znth ((Znth (qh - 0 ) Q 0)) (dl_2) (0))) ” 
  &&  “ ((Znth (qh - 0 ) Q 0) <= n_pre) ” 
  &&  “ (1 <= (Znth (qh - 0 ) Q 0)) ” 
  &&  “ ((Znth (qh - 0 ) Q 0) = (Znth (((qh + 1 ) - 1 )) (Q) (0))) ”
  &&  emp
).

Definition bfs_type_entail_wit_6_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (qh < qt)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (0 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q)))) (PreH16 : (qt <= n_pre)) (PreH17 : ((Zlength (dl_2)) = 100005)) (PreH18 : (BfsCore n_pre edges goods c_pre Q dl_2 )) (PreH19 : (BfsExpanded n_pre edges Q dl_2 qh )) (PreH20 : ((qh < qt) -> (BfsBounded Q dl_2 ((Znth ((Znth (qh) (Q) (0))) (dl_2) (0)) + 1 ) ))) ,
  (BfsBounded Q dl_2 ((Znth ((Znth (qh - 0 ) Q 0)) (dl_2) (0)) + 1 ) )
.

Definition bfs_type_entail_wit_6_split_goal_2 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (qh < qt)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (0 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q)))) (PreH16 : (qt <= n_pre)) (PreH17 : ((Zlength (dl_2)) = 100005)) (PreH18 : (BfsCore n_pre edges goods c_pre Q dl_2 )) (PreH19 : (BfsExpanded n_pre edges Q dl_2 qh )) (PreH20 : ((qh < qt) -> (BfsBounded Q dl_2 ((Znth ((Znth (qh) (Q) (0))) (dl_2) (0)) + 1 ) ))) ,
  (BfsExpanded n_pre edges Q dl_2 ((qh + 1 ) - 1 ) )
.

Definition bfs_type_entail_wit_6_split_goal_3 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (qh < qt)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (0 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q)))) (PreH16 : (qt <= n_pre)) (PreH17 : ((Zlength (dl_2)) = 100005)) (PreH18 : (BfsCore n_pre edges goods c_pre Q dl_2 )) (PreH19 : (BfsExpanded n_pre edges Q dl_2 qh )) (PreH20 : ((qh < qt) -> (BfsBounded Q dl_2 ((Znth ((Znth (qh) (Q) (0))) (dl_2) (0)) + 1 ) ))) ,
  ((Znth ((Znth (qh - 0 ) Q 0)) (dl_2) (0)) <= (n_pre - 1 ))
.

Definition bfs_type_entail_wit_6_split_goal_4 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (qh < qt)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (0 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q)))) (PreH16 : (qt <= n_pre)) (PreH17 : ((Zlength (dl_2)) = 100005)) (PreH18 : (BfsCore n_pre edges goods c_pre Q dl_2 )) (PreH19 : (BfsExpanded n_pre edges Q dl_2 qh )) (PreH20 : ((qh < qt) -> (BfsBounded Q dl_2 ((Znth ((Znth (qh) (Q) (0))) (dl_2) (0)) + 1 ) ))) ,
  (0 <= (Znth ((Znth (qh - 0 ) Q 0)) (dl_2) (0)))
.

Definition bfs_type_entail_wit_6_split_goal_5 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (qh < qt)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (0 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q)))) (PreH16 : (qt <= n_pre)) (PreH17 : ((Zlength (dl_2)) = 100005)) (PreH18 : (BfsCore n_pre edges goods c_pre Q dl_2 )) (PreH19 : (BfsExpanded n_pre edges Q dl_2 qh )) (PreH20 : ((qh < qt) -> (BfsBounded Q dl_2 ((Znth ((Znth (qh) (Q) (0))) (dl_2) (0)) + 1 ) ))) ,
  ((Znth (qh - 0 ) Q 0) <= n_pre)
.

Definition bfs_type_entail_wit_6_split_goal_6 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (qh < qt)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (0 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q)))) (PreH16 : (qt <= n_pre)) (PreH17 : ((Zlength (dl_2)) = 100005)) (PreH18 : (BfsCore n_pre edges goods c_pre Q dl_2 )) (PreH19 : (BfsExpanded n_pre edges Q dl_2 qh )) (PreH20 : ((qh < qt) -> (BfsBounded Q dl_2 ((Znth ((Znth (qh) (Q) (0))) (dl_2) (0)) + 1 ) ))) ,
  (1 <= (Znth (qh - 0 ) Q 0))
.

Definition bfs_type_entail_wit_6_split_goal_7 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (qh < qt)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (0 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q)))) (PreH16 : (qt <= n_pre)) (PreH17 : ((Zlength (dl_2)) = 100005)) (PreH18 : (BfsCore n_pre edges goods c_pre Q dl_2 )) (PreH19 : (BfsExpanded n_pre edges Q dl_2 qh )) (PreH20 : ((qh < qt) -> (BfsBounded Q dl_2 ((Znth ((Znth (qh) (Q) (0))) (dl_2) (0)) + 1 ) ))) ,
  ((Znth (qh - 0 ) Q 0) = (Znth (((qh + 1 ) - 1 )) (Q) (0)))
.

Definition bfs_type_entail_wit_7 := 
(
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q_2: (@list Z)) (qh: Z) (qt: Z) (u: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (0 <= m)) (PreH4 : (m <= 100000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 100)) (PreH7 : (n_pre = (Zlength (goods)))) (PreH8 : (m = (Zlength (edges)))) (PreH9 : (AdjBuild n_pre m edges hd nx tlst )) (PreH10 : (NxtRange m nx )) (PreH11 : (ArcToRange n_pre m tlst )) (PreH12 : (1 <= qh)) (PreH13 : (qh <= qt)) (PreH14 : (qt = (Zlength (Q_2)))) (PreH15 : (qt <= n_pre)) (PreH16 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : (0 <= (Znth (u) (dl_2) (0)))) (PreH20 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH21 : ((Zlength (dl_2)) = 100005)) (PreH22 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH23 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH24 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) ,
  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q_2 )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl_2 )
|--
  EX (dl: (@list Z))  (Q: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= qh) ” 
  &&  “ (qh <= qt) ” 
  &&  “ (qt = (Zlength (Q))) ” 
  &&  “ (qt <= n_pre) ” 
  &&  “ (u = (Znth ((qh - 1 )) (Q) (0))) ” 
  &&  “ (1 <= u) ” 
  &&  “ (u <= n_pre) ” 
  &&  “ (0 <= (Znth (u) (dl) (0))) ” 
  &&  “ ((Znth (u) (dl) (0)) <= (n_pre - 1 )) ” 
  &&  “ ((-1) <= (Znth (u - 1 ) hd 0)) ” 
  &&  “ ((Znth (u - 1 ) hd 0) < (2 * m )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ (((Znth (u - 1 ) hd 0) <> (-1)) -> ((1 <= (Znth ((Znth (u - 1 ) hd 0)) (tlst) (0))) /\ ((Znth ((Znth (u - 1 ) hd 0)) (tlst) (0)) <= n_pre))) ” 
  &&  “ ((((Znth (u - 1 ) hd 0) <> (-1)) /\ ((Znth ((Znth ((Znth (u - 1 ) hd 0)) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre)) ” 
  &&  “ (BfsCore n_pre edges goods c_pre Q dl ) ” 
  &&  “ (BfsExpanded n_pre edges Q dl (qh - 1 ) ) ” 
  &&  “ (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) ) ” 
  &&  “ (BfsScan m edges nx tlst Q dl u (Znth (u - 1 ) hd 0) ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
) \/
(
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q_2: (@list Z)) (qh: Z) (qt: Z) (u: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (0 <= m)) (PreH4 : (m <= 100000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 100)) (PreH7 : (n_pre = (Zlength (goods)))) (PreH8 : (m = (Zlength (edges)))) (PreH9 : (AdjBuild n_pre m edges hd nx tlst )) (PreH10 : (NxtRange m nx )) (PreH11 : (ArcToRange n_pre m tlst )) (PreH12 : (1 <= qh)) (PreH13 : (qh <= qt)) (PreH14 : (qt = (Zlength (Q_2)))) (PreH15 : (qt <= n_pre)) (PreH16 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : (0 <= (Znth (u) (dl_2) (0)))) (PreH20 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH21 : ((Zlength (dl_2)) = 100005)) (PreH22 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH23 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH24 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) ,
  TT && emp 
|--
  “ (BfsScan m edges nx tlst Q_2 dl_2 u (Znth (u - 1 ) hd 0) ) ” 
  &&  “ ((((Znth (u - 1 ) hd 0) <> (-1)) /\ ((Znth ((Znth ((Znth (u - 1 ) hd 0)) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre)) ” 
  &&  “ (((Znth (u - 1 ) hd 0) <> (-1)) -> ((1 <= (Znth ((Znth (u - 1 ) hd 0)) (tlst) (0))) /\ ((Znth ((Znth (u - 1 ) hd 0)) (tlst) (0)) <= n_pre))) ” 
  &&  “ ((Znth (u - 1 ) hd 0) < (2 * m )) ” 
  &&  “ ((-1) <= (Znth (u - 1 ) hd 0)) ”
  &&  emp
).

Definition bfs_type_entail_wit_7_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q_2: (@list Z)) (qh: Z) (qt: Z) (u: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (0 <= m)) (PreH4 : (m <= 100000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 100)) (PreH7 : (n_pre = (Zlength (goods)))) (PreH8 : (m = (Zlength (edges)))) (PreH9 : (AdjBuild n_pre m edges hd nx tlst )) (PreH10 : (NxtRange m nx )) (PreH11 : (ArcToRange n_pre m tlst )) (PreH12 : (1 <= qh)) (PreH13 : (qh <= qt)) (PreH14 : (qt = (Zlength (Q_2)))) (PreH15 : (qt <= n_pre)) (PreH16 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : (0 <= (Znth (u) (dl_2) (0)))) (PreH20 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH21 : ((Zlength (dl_2)) = 100005)) (PreH22 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH23 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH24 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) ,
  (BfsScan m edges nx tlst Q_2 dl_2 u (Znth (u - 1 ) hd 0) )
.

Definition bfs_type_entail_wit_7_split_goal_2 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q_2: (@list Z)) (qh: Z) (qt: Z) (u: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (0 <= m)) (PreH4 : (m <= 100000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 100)) (PreH7 : (n_pre = (Zlength (goods)))) (PreH8 : (m = (Zlength (edges)))) (PreH9 : (AdjBuild n_pre m edges hd nx tlst )) (PreH10 : (NxtRange m nx )) (PreH11 : (ArcToRange n_pre m tlst )) (PreH12 : (1 <= qh)) (PreH13 : (qh <= qt)) (PreH14 : (qt = (Zlength (Q_2)))) (PreH15 : (qt <= n_pre)) (PreH16 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : (0 <= (Znth (u) (dl_2) (0)))) (PreH20 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH21 : ((Zlength (dl_2)) = 100005)) (PreH22 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH23 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH24 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) ,
  ((((Znth (u - 1 ) hd 0) <> (-1)) /\ ((Znth ((Znth ((Znth (u - 1 ) hd 0)) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))
.

Definition bfs_type_entail_wit_7_split_goal_3 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q_2: (@list Z)) (qh: Z) (qt: Z) (u: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (0 <= m)) (PreH4 : (m <= 100000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 100)) (PreH7 : (n_pre = (Zlength (goods)))) (PreH8 : (m = (Zlength (edges)))) (PreH9 : (AdjBuild n_pre m edges hd nx tlst )) (PreH10 : (NxtRange m nx )) (PreH11 : (ArcToRange n_pre m tlst )) (PreH12 : (1 <= qh)) (PreH13 : (qh <= qt)) (PreH14 : (qt = (Zlength (Q_2)))) (PreH15 : (qt <= n_pre)) (PreH16 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : (0 <= (Znth (u) (dl_2) (0)))) (PreH20 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH21 : ((Zlength (dl_2)) = 100005)) (PreH22 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH23 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH24 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) ,
  (((Znth (u - 1 ) hd 0) <> (-1)) -> ((1 <= (Znth ((Znth (u - 1 ) hd 0)) (tlst) (0))) /\ ((Znth ((Znth (u - 1 ) hd 0)) (tlst) (0)) <= n_pre)))
.

Definition bfs_type_entail_wit_7_split_goal_4 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q_2: (@list Z)) (qh: Z) (qt: Z) (u: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (0 <= m)) (PreH4 : (m <= 100000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 100)) (PreH7 : (n_pre = (Zlength (goods)))) (PreH8 : (m = (Zlength (edges)))) (PreH9 : (AdjBuild n_pre m edges hd nx tlst )) (PreH10 : (NxtRange m nx )) (PreH11 : (ArcToRange n_pre m tlst )) (PreH12 : (1 <= qh)) (PreH13 : (qh <= qt)) (PreH14 : (qt = (Zlength (Q_2)))) (PreH15 : (qt <= n_pre)) (PreH16 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : (0 <= (Znth (u) (dl_2) (0)))) (PreH20 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH21 : ((Zlength (dl_2)) = 100005)) (PreH22 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH23 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH24 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) ,
  ((Znth (u - 1 ) hd 0) < (2 * m ))
.

Definition bfs_type_entail_wit_7_split_goal_5 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl_2: (@list Z)) (Q_2: (@list Z)) (qh: Z) (qt: Z) (u: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (0 <= m)) (PreH4 : (m <= 100000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 100)) (PreH7 : (n_pre = (Zlength (goods)))) (PreH8 : (m = (Zlength (edges)))) (PreH9 : (AdjBuild n_pre m edges hd nx tlst )) (PreH10 : (NxtRange m nx )) (PreH11 : (ArcToRange n_pre m tlst )) (PreH12 : (1 <= qh)) (PreH13 : (qh <= qt)) (PreH14 : (qt = (Zlength (Q_2)))) (PreH15 : (qt <= n_pre)) (PreH16 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : (0 <= (Znth (u) (dl_2) (0)))) (PreH20 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH21 : ((Zlength (dl_2)) = 100005)) (PreH22 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH23 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH24 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) ,
  ((-1) <= (Znth (u - 1 ) hd 0))
.

Definition bfs_type_entail_wit_8_1 := 
(
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.seg ( &( "queue_" ) ) 0 (qt + 1 ) (app (Q_2) ((cons ((Znth e tlst 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "queue_" ) ) (qt + 1 ) n_pre )
  **  (IntArray.full dist_pre 100005 (replace_Znth ((Znth e tlst 0)) (((Znth u dl_2 0) + 1 )) (dl_2)) )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
|--
  EX (dl: (@list Z))  (Q: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= qh) ” 
  &&  “ (qh <= (qt + 1 )) ” 
  &&  “ ((qt + 1 ) = (Zlength (Q))) ” 
  &&  “ ((qt + 1 ) <= n_pre) ” 
  &&  “ (u = (Znth ((qh - 1 )) (Q) (0))) ” 
  &&  “ (1 <= u) ” 
  &&  “ (u <= n_pre) ” 
  &&  “ (0 <= (Znth (u) (dl) (0))) ” 
  &&  “ ((Znth (u) (dl) (0)) <= (n_pre - 1 )) ” 
  &&  “ ((-1) <= (Znth e nx 0)) ” 
  &&  “ ((Znth e nx 0) < (2 * m )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ (((Znth e nx 0) <> (-1)) -> ((1 <= (Znth ((Znth e nx 0)) (tlst) (0))) /\ ((Znth ((Znth e nx 0)) (tlst) (0)) <= n_pre))) ” 
  &&  “ ((((Znth e nx 0) <> (-1)) /\ ((Znth ((Znth ((Znth e nx 0)) (tlst) (0))) (dl) (0)) < 0)) -> ((qt + 1 ) < n_pre)) ” 
  &&  “ (BfsCore n_pre edges goods c_pre Q dl ) ” 
  &&  “ (BfsExpanded n_pre edges Q dl (qh - 1 ) ) ” 
  &&  “ (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) ) ” 
  &&  “ (BfsScan m edges nx tlst Q dl u (Znth e nx 0) ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 (qt + 1 ) Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) (qt + 1 ) n_pre )
  **  (IntArray.full dist_pre 100005 dl )
) \/
(
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  TT && emp 
|--
  “ (BfsScan m edges nx tlst (app (Q_2) ((cons ((Znth e tlst 0)) ((@nil Z))))) (replace_Znth ((Znth e tlst 0)) (((Znth u dl_2 0) + 1 )) (dl_2)) u (Znth e nx 0) ) ” 
  &&  “ (BfsBounded (app (Q_2) ((cons ((Znth e tlst 0)) ((@nil Z))))) (replace_Znth ((Znth e tlst 0)) (((Znth u dl_2 0) + 1 )) (dl_2)) ((Znth (u) ((replace_Znth ((Znth e tlst 0)) (((Znth u dl_2 0) + 1 )) (dl_2))) (0)) + 1 ) ) ” 
  &&  “ (BfsExpanded n_pre edges (app (Q_2) ((cons ((Znth e tlst 0)) ((@nil Z))))) (replace_Znth ((Znth e tlst 0)) (((Znth u dl_2 0) + 1 )) (dl_2)) (qh - 1 ) ) ” 
  &&  “ (BfsCore n_pre edges goods c_pre (app (Q_2) ((cons ((Znth e tlst 0)) ((@nil Z))))) (replace_Znth ((Znth e tlst 0)) (((Znth u dl_2 0) + 1 )) (dl_2)) ) ” 
  &&  “ ((((Znth e nx 0) <> (-1)) /\ ((Znth ((Znth ((Znth e nx 0)) (tlst) (0))) ((replace_Znth ((Znth e tlst 0)) (((Znth u dl_2 0) + 1 )) (dl_2))) (0)) < 0)) -> ((qt + 1 ) < n_pre)) ” 
  &&  “ (((Znth e nx 0) <> (-1)) -> ((1 <= (Znth ((Znth e nx 0)) (tlst) (0))) /\ ((Znth ((Znth e nx 0)) (tlst) (0)) <= n_pre))) ” 
  &&  “ ((Zlength ((replace_Znth ((Znth e tlst 0)) (((Znth u dl_2 0) + 1 )) (dl_2)))) = 100005) ” 
  &&  “ ((Znth e nx 0) < (2 * m )) ” 
  &&  “ ((-1) <= (Znth e nx 0)) ” 
  &&  “ ((Znth (u) ((replace_Znth ((Znth e tlst 0)) (((Znth u dl_2 0) + 1 )) (dl_2))) (0)) <= (n_pre - 1 )) ” 
  &&  “ (0 <= (Znth (u) ((replace_Znth ((Znth e tlst 0)) (((Znth u dl_2 0) + 1 )) (dl_2))) (0))) ” 
  &&  “ (u = (Znth ((qh - 1 )) ((app (Q_2) ((cons ((Znth e tlst 0)) ((@nil Z)))))) (0))) ” 
  &&  “ ((qt + 1 ) = (Zlength ((app (Q_2) ((cons ((Znth e tlst 0)) ((@nil Z)))))))) ”
  &&  emp
).

Definition bfs_type_entail_wit_8_1_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  (BfsScan m edges nx tlst (app (Q_2) ((cons ((Znth e tlst 0)) ((@nil Z))))) (replace_Znth ((Znth e tlst 0)) (((Znth u dl_2 0) + 1 )) (dl_2)) u (Znth e nx 0) )
.

Definition bfs_type_entail_wit_8_1_split_goal_2 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  (BfsBounded (app (Q_2) ((cons ((Znth e tlst 0)) ((@nil Z))))) (replace_Znth ((Znth e tlst 0)) (((Znth u dl_2 0) + 1 )) (dl_2)) ((Znth (u) ((replace_Znth ((Znth e tlst 0)) (((Znth u dl_2 0) + 1 )) (dl_2))) (0)) + 1 ) )
.

Definition bfs_type_entail_wit_8_1_split_goal_3 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  (BfsExpanded n_pre edges (app (Q_2) ((cons ((Znth e tlst 0)) ((@nil Z))))) (replace_Znth ((Znth e tlst 0)) (((Znth u dl_2 0) + 1 )) (dl_2)) (qh - 1 ) )
.

Definition bfs_type_entail_wit_8_1_split_goal_4 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  (BfsCore n_pre edges goods c_pre (app (Q_2) ((cons ((Znth e tlst 0)) ((@nil Z))))) (replace_Znth ((Znth e tlst 0)) (((Znth u dl_2 0) + 1 )) (dl_2)) )
.

Definition bfs_type_entail_wit_8_1_split_goal_5 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  ((((Znth e nx 0) <> (-1)) /\ ((Znth ((Znth ((Znth e nx 0)) (tlst) (0))) ((replace_Znth ((Znth e tlst 0)) (((Znth u dl_2 0) + 1 )) (dl_2))) (0)) < 0)) -> ((qt + 1 ) < n_pre))
.

Definition bfs_type_entail_wit_8_1_split_goal_6 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  (((Znth e nx 0) <> (-1)) -> ((1 <= (Znth ((Znth e nx 0)) (tlst) (0))) /\ ((Znth ((Znth e nx 0)) (tlst) (0)) <= n_pre)))
.

Definition bfs_type_entail_wit_8_1_split_goal_7 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  ((Zlength ((replace_Znth ((Znth e tlst 0)) (((Znth u dl_2 0) + 1 )) (dl_2)))) = 100005)
.

Definition bfs_type_entail_wit_8_1_split_goal_8 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  ((Znth e nx 0) < (2 * m ))
.

Definition bfs_type_entail_wit_8_1_split_goal_9 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  ((-1) <= (Znth e nx 0))
.

Definition bfs_type_entail_wit_8_1_split_goal_10 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  ((Znth (u) ((replace_Znth ((Znth e tlst 0)) (((Znth u dl_2 0) + 1 )) (dl_2))) (0)) <= (n_pre - 1 ))
.

Definition bfs_type_entail_wit_8_1_split_goal_11 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  (0 <= (Znth (u) ((replace_Znth ((Znth e tlst 0)) (((Znth u dl_2 0) + 1 )) (dl_2))) (0)))
.

Definition bfs_type_entail_wit_8_1_split_goal_12 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  (u = (Znth ((qh - 1 )) ((app (Q_2) ((cons ((Znth e tlst 0)) ((@nil Z)))))) (0)))
.

Definition bfs_type_entail_wit_8_1_split_goal_13 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  ((qt + 1 ) = (Zlength ((app (Q_2) ((cons ((Znth e tlst 0)) ((@nil Z))))))))
.

Definition bfs_type_entail_wit_8_2 := 
(
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) >= 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full dist_pre 100005 dl_2 )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q_2 )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
|--
  EX (dl: (@list Z))  (Q: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= qh) ” 
  &&  “ (qh <= qt) ” 
  &&  “ (qt = (Zlength (Q))) ” 
  &&  “ (qt <= n_pre) ” 
  &&  “ (u = (Znth ((qh - 1 )) (Q) (0))) ” 
  &&  “ (1 <= u) ” 
  &&  “ (u <= n_pre) ” 
  &&  “ (0 <= (Znth (u) (dl) (0))) ” 
  &&  “ ((Znth (u) (dl) (0)) <= (n_pre - 1 )) ” 
  &&  “ ((-1) <= (Znth e nx 0)) ” 
  &&  “ ((Znth e nx 0) < (2 * m )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ (((Znth e nx 0) <> (-1)) -> ((1 <= (Znth ((Znth e nx 0)) (tlst) (0))) /\ ((Znth ((Znth e nx 0)) (tlst) (0)) <= n_pre))) ” 
  &&  “ ((((Znth e nx 0) <> (-1)) /\ ((Znth ((Znth ((Znth e nx 0)) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre)) ” 
  &&  “ (BfsCore n_pre edges goods c_pre Q dl ) ” 
  &&  “ (BfsExpanded n_pre edges Q dl (qh - 1 ) ) ” 
  &&  “ (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) ) ” 
  &&  “ (BfsScan m edges nx tlst Q dl u (Znth e nx 0) ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
) \/
(
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) >= 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  TT && emp 
|--
  “ (BfsScan m edges nx tlst Q_2 dl_2 u (Znth e nx 0) ) ” 
  &&  “ ((((Znth e nx 0) <> (-1)) /\ ((Znth ((Znth ((Znth e nx 0)) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre)) ” 
  &&  “ (((Znth e nx 0) <> (-1)) -> ((1 <= (Znth ((Znth e nx 0)) (tlst) (0))) /\ ((Znth ((Znth e nx 0)) (tlst) (0)) <= n_pre))) ” 
  &&  “ ((Znth e nx 0) < (2 * m )) ” 
  &&  “ ((-1) <= (Znth e nx 0)) ”
  &&  emp
).

Definition bfs_type_entail_wit_8_2_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) >= 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  (BfsScan m edges nx tlst Q_2 dl_2 u (Znth e nx 0) )
.

Definition bfs_type_entail_wit_8_2_split_goal_2 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) >= 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  ((((Znth e nx 0) <> (-1)) /\ ((Znth ((Znth ((Znth e nx 0)) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))
.

Definition bfs_type_entail_wit_8_2_split_goal_3 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) >= 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  (((Znth e nx 0) <> (-1)) -> ((1 <= (Znth ((Znth e nx 0)) (tlst) (0))) /\ ((Znth ((Znth e nx 0)) (tlst) (0)) <= n_pre)))
.

Definition bfs_type_entail_wit_8_2_split_goal_4 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) >= 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  ((Znth e nx 0) < (2 * m ))
.

Definition bfs_type_entail_wit_8_2_split_goal_5 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl_2 0) >= 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q_2)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl_2) (0)))) (PreH22 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl_2)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH29 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH30 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  ((-1) <= (Znth e nx 0))
.

Definition bfs_type_entail_wit_9 := 
(
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (e = (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q_2)))) (PreH16 : (qt <= n_pre)) (PreH17 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH18 : (1 <= u)) (PreH19 : (u <= n_pre)) (PreH20 : (0 <= (Znth (u) (dl_2) (0)))) (PreH21 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH22 : ((-1) <= e)) (PreH23 : (e < (2 * m ))) (PreH24 : ((Zlength (dl_2)) = 100005)) (PreH25 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH26 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH27 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH28 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH29 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH30 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q_2 )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl_2 )
|--
  EX (dl: (@list Z))  (Q: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (0 <= qh) ” 
  &&  “ (qh <= qt) ” 
  &&  “ (qt = (Zlength (Q))) ” 
  &&  “ (qt <= n_pre) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ (BfsCore n_pre edges goods c_pre Q dl ) ” 
  &&  “ (BfsExpanded n_pre edges Q dl qh ) ” 
  &&  “ ((qh < qt) -> (BfsBounded Q dl ((Znth ((Znth (qh) (Q) (0))) (dl) (0)) + 1 ) )) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
) \/
(
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (e = (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q_2)))) (PreH16 : (qt <= n_pre)) (PreH17 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH18 : (1 <= u)) (PreH19 : (u <= n_pre)) (PreH20 : (0 <= (Znth (u) (dl_2) (0)))) (PreH21 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH22 : ((-1) <= e)) (PreH23 : (e < (2 * m ))) (PreH24 : ((Zlength (dl_2)) = 100005)) (PreH25 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH26 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH27 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH28 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH29 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH30 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  TT && emp 
|--
  “ ((qh < qt) -> (BfsBounded Q_2 dl_2 ((Znth ((Znth (qh) (Q_2) (0))) (dl_2) (0)) + 1 ) )) ” 
  &&  “ (BfsExpanded n_pre edges Q_2 dl_2 qh ) ”
  &&  emp
).

Definition bfs_type_entail_wit_9_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (e = (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q_2)))) (PreH16 : (qt <= n_pre)) (PreH17 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH18 : (1 <= u)) (PreH19 : (u <= n_pre)) (PreH20 : (0 <= (Znth (u) (dl_2) (0)))) (PreH21 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH22 : ((-1) <= e)) (PreH23 : (e < (2 * m ))) (PreH24 : ((Zlength (dl_2)) = 100005)) (PreH25 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH26 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH27 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH28 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH29 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH30 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  ((qh < qt) -> (BfsBounded Q_2 dl_2 ((Znth ((Znth (qh) (Q_2) (0))) (dl_2) (0)) + 1 ) ))
.

Definition bfs_type_entail_wit_9_split_goal_2 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl_2: (@list Z)) (u: Z) (Q_2: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (e = (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q_2)))) (PreH16 : (qt <= n_pre)) (PreH17 : (u = (Znth ((qh - 1 )) (Q_2) (0)))) (PreH18 : (1 <= u)) (PreH19 : (u <= n_pre)) (PreH20 : (0 <= (Znth (u) (dl_2) (0)))) (PreH21 : ((Znth (u) (dl_2) (0)) <= (n_pre - 1 ))) (PreH22 : ((-1) <= e)) (PreH23 : (e < (2 * m ))) (PreH24 : ((Zlength (dl_2)) = 100005)) (PreH25 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH26 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl_2) (0)) < 0)) -> (qt < n_pre))) (PreH27 : (BfsCore n_pre edges goods c_pre Q_2 dl_2 )) (PreH28 : (BfsExpanded n_pre edges Q_2 dl_2 (qh - 1 ) )) (PreH29 : (BfsBounded Q_2 dl_2 ((Znth (u) (dl_2) (0)) + 1 ) )) (PreH30 : (BfsScan m edges nx tlst Q_2 dl_2 u e )) ,
  (BfsExpanded n_pre edges Q_2 dl_2 qh )
.

Definition bfs_type_return_wit_1 := 
(
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (qh >= qt)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (0 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q)))) (PreH16 : (qt <= n_pre)) (PreH17 : ((Zlength (dl)) = 100005)) (PreH18 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH19 : (BfsExpanded n_pre edges Q dl qh )) (PreH20 : ((qh < qt) -> (BfsBounded Q dl ((Znth ((Znth (qh) (Q) (0))) (dl) (0)) + 1 ) ))) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
|--
  EX (dist_after: (@list Z)) ,
  “ ((Zlength (dist_after)) = 100005) ” 
  &&  “ (BfsRowResult n_pre edges goods c_pre dist_after ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full dist_pre 100005 dist_after )
) \/
(
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (qh >= qt)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (0 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q)))) (PreH16 : (qt <= n_pre)) (PreH17 : ((Zlength (dl)) = 100005)) (PreH18 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH19 : (BfsExpanded n_pre edges Q dl qh )) (PreH20 : ((qh < qt) -> (BfsBounded Q dl ((Znth ((Znth (qh) (Q) (0))) (dl) (0)) + 1 ) ))) ,
  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
|--
  “ (BfsRowResult n_pre edges goods c_pre dl ) ”
  &&  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
).

Definition bfs_type_return_wit_1_split_goal_1 := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (qh >= qt)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (0 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q)))) (PreH16 : (qt <= n_pre)) (PreH17 : ((Zlength (dl)) = 100005)) (PreH18 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH19 : (BfsExpanded n_pre edges Q dl qh )) (PreH20 : ((qh < qt) -> (BfsBounded Q dl ((Znth ((Znth (qh) (Q) (0))) (dl) (0)) + 1 ) ))) ,
  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
|--
  “ (BfsRowResult n_pre edges goods c_pre dl ) ”
.

Definition bfs_type_return_wit_1_split_goal_spatial := 
forall (c_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (qh >= qt)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (0 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q)))) (PreH16 : (qt <= n_pre)) (PreH17 : ((Zlength (dl)) = 100005)) (PreH18 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH19 : (BfsExpanded n_pre edges Q dl qh )) (PreH20 : ((qh < qt) -> (BfsBounded Q dl ((Znth ((Znth (qh) (Q) (0))) (dl) (0)) + 1 ) ))) ,
  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
|--
  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
.

Definition bfs_type_partial_solve_wit_1 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= v)) (PreH14 : (v <= (n_pre + 1 ))) (PreH15 : ((Zlength (dl)) = 100005)) (PreH16 : forall (w: Z) , (((1 <= w) /\ (w < v)) -> ((Znth (w) (dl) (0)) = (-1)))) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full dist_pre 100005 dl )
|--
  “ (v <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ forall (w: Z) , (((1 <= w) /\ (w < v)) -> ((Znth (w) (dl) (0)) = (-1))) ”
  &&  (((dist_pre + (v * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i dist_pre v 0 100005 dl )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
.

Definition bfs_type_partial_solve_wit_2 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= v)) (PreH14 : (v <= (n_pre + 1 ))) (PreH15 : (qh = 0)) (PreH16 : (0 <= qt)) (PreH17 : (qt = (Zlength (Q)))) (PreH18 : (qt <= (v - 1 ))) (PreH19 : ((Zlength (dl)) = 100005)) (PreH20 : (BfsInit n_pre goods c_pre Q dl v )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
|--
  “ (v <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= (n_pre + 1 )) ” 
  &&  “ (qh = 0) ” 
  &&  “ (0 <= qt) ” 
  &&  “ (qt = (Zlength (Q))) ” 
  &&  “ (qt <= (v - 1 )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ (BfsInit n_pre goods c_pre Q dl v ) ”
  &&  (((a_pre + (v * sizeof(INT)))) # Int  |-> (Znth (v - 1 ) goods 0))
  **  (IntArray.missing_i a_pre v 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
.

Definition bfs_type_partial_solve_wit_3 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : ((Znth (v - 1 ) goods 0) = c_pre)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= v)) (PreH15 : (v <= (n_pre + 1 ))) (PreH16 : (qh = 0)) (PreH17 : (0 <= qt)) (PreH18 : (qt = (Zlength (Q)))) (PreH19 : (qt <= (v - 1 ))) (PreH20 : ((Zlength (dl)) = 100005)) (PreH21 : (BfsInit n_pre goods c_pre Q dl v )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
|--
  “ ((Znth (v - 1 ) goods 0) = c_pre) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= (n_pre + 1 )) ” 
  &&  “ (qh = 0) ” 
  &&  “ (0 <= qt) ” 
  &&  “ (qt = (Zlength (Q))) ” 
  &&  “ (qt <= (v - 1 )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ (BfsInit n_pre goods c_pre Q dl v ) ”
  &&  (((dist_pre + (v * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i dist_pre v 0 100005 dl )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
.

Definition bfs_type_partial_solve_wit_4 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (v: Z) (PreH1 : ((Znth (v - 1 ) goods 0) = c_pre)) (PreH2 : (v <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= v)) (PreH15 : (v <= (n_pre + 1 ))) (PreH16 : (qh = 0)) (PreH17 : (0 <= qt)) (PreH18 : (qt = (Zlength (Q)))) (PreH19 : (qt <= (v - 1 ))) (PreH20 : ((Zlength (dl)) = 100005)) (PreH21 : (BfsInit n_pre goods c_pre Q dl v )) ,
  (IntArray.full dist_pre 100005 (replace_Znth (v) (0) (dl)) )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
|--
  “ ((Znth (v - 1 ) goods 0) = c_pre) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= (n_pre + 1 )) ” 
  &&  “ (qh = 0) ” 
  &&  “ (0 <= qt) ” 
  &&  “ (qt = (Zlength (Q))) ” 
  &&  “ (qt <= (v - 1 )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ (BfsInit n_pre goods c_pre Q dl v ) ”
  &&  (((( &( "queue_" ) ) + (qt * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "queue_" ) ) (qt + 1 ) n_pre )
  **  (IntArray.full dist_pre 100005 (replace_Znth (v) (0) (dl)) )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
.

Definition bfs_type_partial_solve_wit_5 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (qh < qt)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (0 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q)))) (PreH16 : (qt <= n_pre)) (PreH17 : ((Zlength (dl)) = 100005)) (PreH18 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH19 : (BfsExpanded n_pre edges Q dl qh )) (PreH20 : ((qh < qt) -> (BfsBounded Q dl ((Znth ((Znth (qh) (Q) (0))) (dl) (0)) + 1 ) ))) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
|--
  “ (qh < qt) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (0 <= qh) ” 
  &&  “ (qh <= qt) ” 
  &&  “ (qt = (Zlength (Q))) ” 
  &&  “ (qt <= n_pre) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ (BfsCore n_pre edges goods c_pre Q dl ) ” 
  &&  “ (BfsExpanded n_pre edges Q dl qh ) ” 
  &&  “ ((qh < qt) -> (BfsBounded Q dl ((Znth ((Znth (qh) (Q) (0))) (dl) (0)) + 1 ) )) ”
  &&  (((( &( "queue_" ) ) + (qh * sizeof(INT)))) # Int  |-> (Znth (qh - 0 ) Q 0))
  **  (IntArray.missing_i ( &( "queue_" ) ) qh 0 qt Q )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
.

Definition bfs_type_partial_solve_wit_6 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (dl: (@list Z)) (Q: (@list Z)) (qh: Z) (qt: Z) (u: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (0 <= m)) (PreH4 : (m <= 100000)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 100)) (PreH7 : (n_pre = (Zlength (goods)))) (PreH8 : (m = (Zlength (edges)))) (PreH9 : (AdjBuild n_pre m edges hd nx tlst )) (PreH10 : (NxtRange m nx )) (PreH11 : (ArcToRange n_pre m tlst )) (PreH12 : (1 <= qh)) (PreH13 : (qh <= qt)) (PreH14 : (qt = (Zlength (Q)))) (PreH15 : (qt <= n_pre)) (PreH16 : (u = (Znth ((qh - 1 )) (Q) (0)))) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : (0 <= (Znth (u) (dl) (0)))) (PreH20 : ((Znth (u) (dl) (0)) <= (n_pre - 1 ))) (PreH21 : ((Zlength (dl)) = 100005)) (PreH22 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH23 : (BfsExpanded n_pre edges Q dl (qh - 1 ) )) (PreH24 : (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= qh) ” 
  &&  “ (qh <= qt) ” 
  &&  “ (qt = (Zlength (Q))) ” 
  &&  “ (qt <= n_pre) ” 
  &&  “ (u = (Znth ((qh - 1 )) (Q) (0))) ” 
  &&  “ (1 <= u) ” 
  &&  “ (u <= n_pre) ” 
  &&  “ (0 <= (Znth (u) (dl) (0))) ” 
  &&  “ ((Znth (u) (dl) (0)) <= (n_pre - 1 )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ (BfsCore n_pre edges goods c_pre Q dl ) ” 
  &&  “ (BfsExpanded n_pre edges Q dl (qh - 1 ) ) ” 
  &&  “ (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) ) ”
  &&  (((( &( "head_" ) ) + (u * sizeof(INT)))) # Int  |-> (Znth (u - 1 ) hd 0))
  **  (IntArray.missing_i ( &( "head_" ) ) u 1 (n_pre + 1 ) hd )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
.

Definition bfs_type_partial_solve_wit_7 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl: (@list Z)) (u: Z) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (e <> (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q)))) (PreH16 : (qt <= n_pre)) (PreH17 : (u = (Znth ((qh - 1 )) (Q) (0)))) (PreH18 : (1 <= u)) (PreH19 : (u <= n_pre)) (PreH20 : (0 <= (Znth (u) (dl) (0)))) (PreH21 : ((Znth (u) (dl) (0)) <= (n_pre - 1 ))) (PreH22 : ((-1) <= e)) (PreH23 : (e < (2 * m ))) (PreH24 : ((Zlength (dl)) = 100005)) (PreH25 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH26 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre))) (PreH27 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH28 : (BfsExpanded n_pre edges Q dl (qh - 1 ) )) (PreH29 : (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) )) (PreH30 : (BfsScan m edges nx tlst Q dl u e )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
|--
  “ (e <> (-1)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= qh) ” 
  &&  “ (qh <= qt) ” 
  &&  “ (qt = (Zlength (Q))) ” 
  &&  “ (qt <= n_pre) ” 
  &&  “ (u = (Znth ((qh - 1 )) (Q) (0))) ” 
  &&  “ (1 <= u) ” 
  &&  “ (u <= n_pre) ” 
  &&  “ (0 <= (Znth (u) (dl) (0))) ” 
  &&  “ ((Znth (u) (dl) (0)) <= (n_pre - 1 )) ” 
  &&  “ ((-1) <= e) ” 
  &&  “ (e < (2 * m )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre))) ” 
  &&  “ (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre)) ” 
  &&  “ (BfsCore n_pre edges goods c_pre Q dl ) ” 
  &&  “ (BfsExpanded n_pre edges Q dl (qh - 1 ) ) ” 
  &&  “ (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) ) ” 
  &&  “ (BfsScan m edges nx tlst Q dl u e ) ”
  &&  (((( &( "to_" ) ) + (e * sizeof(INT)))) # Int  |-> (Znth e tlst 0))
  **  (IntArray.missing_i ( &( "to_" ) ) e 0 (2 * m ) tlst )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
.

Definition bfs_type_partial_solve_wit_8 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl: (@list Z)) (u: Z) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : (e <> (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m)) (PreH5 : (m <= 100000)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (n_pre = (Zlength (goods)))) (PreH9 : (m = (Zlength (edges)))) (PreH10 : (AdjBuild n_pre m edges hd nx tlst )) (PreH11 : (NxtRange m nx )) (PreH12 : (ArcToRange n_pre m tlst )) (PreH13 : (1 <= qh)) (PreH14 : (qh <= qt)) (PreH15 : (qt = (Zlength (Q)))) (PreH16 : (qt <= n_pre)) (PreH17 : (u = (Znth ((qh - 1 )) (Q) (0)))) (PreH18 : (1 <= u)) (PreH19 : (u <= n_pre)) (PreH20 : (0 <= (Znth (u) (dl) (0)))) (PreH21 : ((Znth (u) (dl) (0)) <= (n_pre - 1 ))) (PreH22 : ((-1) <= e)) (PreH23 : (e < (2 * m ))) (PreH24 : ((Zlength (dl)) = 100005)) (PreH25 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH26 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre))) (PreH27 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH28 : (BfsExpanded n_pre edges Q dl (qh - 1 ) )) (PreH29 : (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) )) (PreH30 : (BfsScan m edges nx tlst Q dl u e )) ,
  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
  **  (IntArray.full dist_pre 100005 dl )
|--
  “ (e <> (-1)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= qh) ” 
  &&  “ (qh <= qt) ” 
  &&  “ (qt = (Zlength (Q))) ” 
  &&  “ (qt <= n_pre) ” 
  &&  “ (u = (Znth ((qh - 1 )) (Q) (0))) ” 
  &&  “ (1 <= u) ” 
  &&  “ (u <= n_pre) ” 
  &&  “ (0 <= (Znth (u) (dl) (0))) ” 
  &&  “ ((Znth (u) (dl) (0)) <= (n_pre - 1 )) ” 
  &&  “ ((-1) <= e) ” 
  &&  “ (e < (2 * m )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre))) ” 
  &&  “ (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre)) ” 
  &&  “ (BfsCore n_pre edges goods c_pre Q dl ) ” 
  &&  “ (BfsExpanded n_pre edges Q dl (qh - 1 ) ) ” 
  &&  “ (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) ) ” 
  &&  “ (BfsScan m edges nx tlst Q dl u e ) ”
  &&  (((dist_pre + ((Znth e tlst 0) * sizeof(INT)))) # Int  |-> (Znth (Znth e tlst 0) dl 0))
  **  (IntArray.missing_i dist_pre (Znth e tlst 0) 0 100005 dl )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
.

Definition bfs_type_partial_solve_wit_9 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl: (@list Z)) (u: Z) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl) (0)))) (PreH22 : ((Znth (u) (dl) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH29 : (BfsExpanded n_pre edges Q dl (qh - 1 ) )) (PreH30 : (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q dl u e )) ,
  (IntArray.full dist_pre 100005 dl )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
|--
  “ ((Znth (Znth e tlst 0) dl 0) < 0) ” 
  &&  “ (e <> (-1)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= qh) ” 
  &&  “ (qh <= qt) ” 
  &&  “ (qt = (Zlength (Q))) ” 
  &&  “ (qt <= n_pre) ” 
  &&  “ (u = (Znth ((qh - 1 )) (Q) (0))) ” 
  &&  “ (1 <= u) ” 
  &&  “ (u <= n_pre) ” 
  &&  “ (0 <= (Znth (u) (dl) (0))) ” 
  &&  “ ((Znth (u) (dl) (0)) <= (n_pre - 1 )) ” 
  &&  “ ((-1) <= e) ” 
  &&  “ (e < (2 * m )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre))) ” 
  &&  “ (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre)) ” 
  &&  “ (BfsCore n_pre edges goods c_pre Q dl ) ” 
  &&  “ (BfsExpanded n_pre edges Q dl (qh - 1 ) ) ” 
  &&  “ (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) ) ” 
  &&  “ (BfsScan m edges nx tlst Q dl u e ) ”
  &&  (((dist_pre + (u * sizeof(INT)))) # Int  |-> (Znth u dl 0))
  **  (IntArray.missing_i dist_pre u 0 100005 dl )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
.

Definition bfs_type_partial_solve_wit_10 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl: (@list Z)) (u: Z) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl) (0)))) (PreH22 : ((Znth (u) (dl) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH29 : (BfsExpanded n_pre edges Q dl (qh - 1 ) )) (PreH30 : (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q dl u e )) ,
  (IntArray.full dist_pre 100005 dl )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
|--
  “ ((Znth (Znth e tlst 0) dl 0) < 0) ” 
  &&  “ (e <> (-1)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= qh) ” 
  &&  “ (qh <= qt) ” 
  &&  “ (qt = (Zlength (Q))) ” 
  &&  “ (qt <= n_pre) ” 
  &&  “ (u = (Znth ((qh - 1 )) (Q) (0))) ” 
  &&  “ (1 <= u) ” 
  &&  “ (u <= n_pre) ” 
  &&  “ (0 <= (Znth (u) (dl) (0))) ” 
  &&  “ ((Znth (u) (dl) (0)) <= (n_pre - 1 )) ” 
  &&  “ ((-1) <= e) ” 
  &&  “ (e < (2 * m )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre))) ” 
  &&  “ (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre)) ” 
  &&  “ (BfsCore n_pre edges goods c_pre Q dl ) ” 
  &&  “ (BfsExpanded n_pre edges Q dl (qh - 1 ) ) ” 
  &&  “ (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) ) ” 
  &&  “ (BfsScan m edges nx tlst Q dl u e ) ”
  &&  (((dist_pre + ((Znth e tlst 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i dist_pre (Znth e tlst 0) 0 100005 dl )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
.

Definition bfs_type_partial_solve_wit_11 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl: (@list Z)) (u: Z) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl) (0)))) (PreH22 : ((Znth (u) (dl) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH29 : (BfsExpanded n_pre edges Q dl (qh - 1 ) )) (PreH30 : (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q dl u e )) ,
  (IntArray.full dist_pre 100005 (replace_Znth ((Znth e tlst 0)) (((Znth u dl 0) + 1 )) (dl)) )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
|--
  “ ((Znth (Znth e tlst 0) dl 0) < 0) ” 
  &&  “ (e <> (-1)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= qh) ” 
  &&  “ (qh <= qt) ” 
  &&  “ (qt = (Zlength (Q))) ” 
  &&  “ (qt <= n_pre) ” 
  &&  “ (u = (Znth ((qh - 1 )) (Q) (0))) ” 
  &&  “ (1 <= u) ” 
  &&  “ (u <= n_pre) ” 
  &&  “ (0 <= (Znth (u) (dl) (0))) ” 
  &&  “ ((Znth (u) (dl) (0)) <= (n_pre - 1 )) ” 
  &&  “ ((-1) <= e) ” 
  &&  “ (e < (2 * m )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre))) ” 
  &&  “ (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre)) ” 
  &&  “ (BfsCore n_pre edges goods c_pre Q dl ) ” 
  &&  “ (BfsExpanded n_pre edges Q dl (qh - 1 ) ) ” 
  &&  “ (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) ) ” 
  &&  “ (BfsScan m edges nx tlst Q dl u e ) ”
  &&  (((( &( "queue_" ) ) + (qt * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "queue_" ) ) (qt + 1 ) n_pre )
  **  (IntArray.full dist_pre 100005 (replace_Znth ((Znth e tlst 0)) (((Znth u dl 0) + 1 )) (dl)) )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
.

Definition bfs_type_partial_solve_wit_12 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl: (@list Z)) (u: Z) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl 0) < 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl) (0)))) (PreH22 : ((Znth (u) (dl) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH29 : (BfsExpanded n_pre edges Q dl (qh - 1 ) )) (PreH30 : (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q dl u e )) ,
  (IntArray.seg ( &( "queue_" ) ) 0 (qt + 1 ) (app (Q) ((cons ((Znth e tlst 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "queue_" ) ) (qt + 1 ) n_pre )
  **  (IntArray.full dist_pre 100005 (replace_Znth ((Znth e tlst 0)) (((Znth u dl 0) + 1 )) (dl)) )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
|--
  “ ((Znth (Znth e tlst 0) dl 0) < 0) ” 
  &&  “ (e <> (-1)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= qh) ” 
  &&  “ (qh <= qt) ” 
  &&  “ (qt = (Zlength (Q))) ” 
  &&  “ (qt <= n_pre) ” 
  &&  “ (u = (Znth ((qh - 1 )) (Q) (0))) ” 
  &&  “ (1 <= u) ” 
  &&  “ (u <= n_pre) ” 
  &&  “ (0 <= (Znth (u) (dl) (0))) ” 
  &&  “ ((Znth (u) (dl) (0)) <= (n_pre - 1 )) ” 
  &&  “ ((-1) <= e) ” 
  &&  “ (e < (2 * m )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre))) ” 
  &&  “ (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre)) ” 
  &&  “ (BfsCore n_pre edges goods c_pre Q dl ) ” 
  &&  “ (BfsExpanded n_pre edges Q dl (qh - 1 ) ) ” 
  &&  “ (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) ) ” 
  &&  “ (BfsScan m edges nx tlst Q dl u e ) ”
  &&  (((( &( "nxt_" ) ) + (e * sizeof(INT)))) # Int  |-> (Znth e nx 0))
  **  (IntArray.missing_i ( &( "nxt_" ) ) e 0 (2 * m ) nx )
  **  (IntArray.seg ( &( "queue_" ) ) 0 (qt + 1 ) (app (Q) ((cons ((Znth e tlst 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "queue_" ) ) (qt + 1 ) n_pre )
  **  (IntArray.full dist_pre 100005 (replace_Znth ((Znth e tlst 0)) (((Znth u dl 0) + 1 )) (dl)) )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
.

Definition bfs_type_partial_solve_wit_13 := 
forall (dist_pre: Z) (c_pre: Z) (a_pre: Z) (n_pre: Z) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (goods: (@list Z)) (edges: (@list (Z * Z))) (m: Z) (e: Z) (dl: (@list Z)) (u: Z) (Q: (@list Z)) (qt: Z) (qh: Z) (PreH1 : ((Znth (Znth e tlst 0) dl 0) >= 0)) (PreH2 : (e <> (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m)) (PreH6 : (m <= 100000)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (n_pre = (Zlength (goods)))) (PreH10 : (m = (Zlength (edges)))) (PreH11 : (AdjBuild n_pre m edges hd nx tlst )) (PreH12 : (NxtRange m nx )) (PreH13 : (ArcToRange n_pre m tlst )) (PreH14 : (1 <= qh)) (PreH15 : (qh <= qt)) (PreH16 : (qt = (Zlength (Q)))) (PreH17 : (qt <= n_pre)) (PreH18 : (u = (Znth ((qh - 1 )) (Q) (0)))) (PreH19 : (1 <= u)) (PreH20 : (u <= n_pre)) (PreH21 : (0 <= (Znth (u) (dl) (0)))) (PreH22 : ((Znth (u) (dl) (0)) <= (n_pre - 1 ))) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m ))) (PreH25 : ((Zlength (dl)) = 100005)) (PreH26 : ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre)))) (PreH27 : (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre))) (PreH28 : (BfsCore n_pre edges goods c_pre Q dl )) (PreH29 : (BfsExpanded n_pre edges Q dl (qh - 1 ) )) (PreH30 : (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) )) (PreH31 : (BfsScan m edges nx tlst Q dl u e )) ,
  (IntArray.full dist_pre 100005 dl )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m ) nx )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
|--
  “ ((Znth (Znth e tlst 0) dl 0) >= 0) ” 
  &&  “ (e <> (-1)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m <= 100000) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m = (Zlength (edges))) ” 
  &&  “ (AdjBuild n_pre m edges hd nx tlst ) ” 
  &&  “ (NxtRange m nx ) ” 
  &&  “ (ArcToRange n_pre m tlst ) ” 
  &&  “ (1 <= qh) ” 
  &&  “ (qh <= qt) ” 
  &&  “ (qt = (Zlength (Q))) ” 
  &&  “ (qt <= n_pre) ” 
  &&  “ (u = (Znth ((qh - 1 )) (Q) (0))) ” 
  &&  “ (1 <= u) ” 
  &&  “ (u <= n_pre) ” 
  &&  “ (0 <= (Znth (u) (dl) (0))) ” 
  &&  “ ((Znth (u) (dl) (0)) <= (n_pre - 1 )) ” 
  &&  “ ((-1) <= e) ” 
  &&  “ (e < (2 * m )) ” 
  &&  “ ((Zlength (dl)) = 100005) ” 
  &&  “ ((e <> (-1)) -> ((1 <= (Znth (e) (tlst) (0))) /\ ((Znth (e) (tlst) (0)) <= n_pre))) ” 
  &&  “ (((e <> (-1)) /\ ((Znth ((Znth (e) (tlst) (0))) (dl) (0)) < 0)) -> (qt < n_pre)) ” 
  &&  “ (BfsCore n_pre edges goods c_pre Q dl ) ” 
  &&  “ (BfsExpanded n_pre edges Q dl (qh - 1 ) ) ” 
  &&  “ (BfsBounded Q dl ((Znth (u) (dl) (0)) + 1 ) ) ” 
  &&  “ (BfsScan m edges nx tlst Q dl u e ) ”
  &&  (((( &( "nxt_" ) ) + (e * sizeof(INT)))) # Int  |-> (Znth e nx 0))
  **  (IntArray.missing_i ( &( "nxt_" ) ) e 0 (2 * m ) nx )
  **  (IntArray.full dist_pre 100005 dl )
  **  (IntArray.full ( &( "to_" ) ) (2 * m ) tlst )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.seg ( &( "queue_" ) ) 0 qt Q )
  **  (IntArray.undef_seg ( &( "queue_" ) ) qt n_pre )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (Pre k_pre s_pre tree_edges goods )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (1 <= s_pre)) (PreH7 : (s_pre <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (k_pre <= n_pre)) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (tree_edges)))) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH12 : (n_pre = (Zlength (goods)))) (PreH13 : (m_pre = (Zlength (tree_edges)))) (PreH14 : ((Zlength (edge_u)) = m_pre)) (PreH15 : ((Zlength (edge_v)) = m_pre)) (PreH16 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH17 : ((Zlength (dist_before)) = 105)) (PreH18 : forall (c: Z) , (((0 <= c) /\ (c < 105)) -> ((Zlength ((Znth c dist_before __default__List_Z))) = 100005))) ,
  ((( &( "v" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_seg ( &( "head_" ) ) 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "nxt_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "to_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_2 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd0: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= (n_pre + 1 ))) (PreH20 : ((Zlength (hd0)) = (v - 1 ))) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < (v - 1 ))) -> ((Znth j hd0 0) = (-1)))) (PreH22 : ((Zlength (dist_before)) = 105)) (PreH23 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg ( &( "head_" ) ) 1 (v + 1 ) (app (hd0) ((cons ((-1)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "head_" ) ) (v + 1 ) (n_pre + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "nxt_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "to_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition solver_safety_wit_3 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd0: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= (n_pre + 1 ))) (PreH20 : ((Zlength (hd0)) = (v - 1 ))) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < (v - 1 ))) -> ((Znth j hd0 0) = (-1)))) (PreH22 : ((Zlength (dist_before)) = 105)) (PreH23 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 v hd0 )
  **  (IntArray.undef_seg ( &( "head_" ) ) v (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "nxt_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "to_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_4 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd0: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= (n_pre + 1 ))) (PreH20 : ((Zlength (hd0)) = (v - 1 ))) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < (v - 1 ))) -> ((Znth j hd0 0) = (-1)))) (PreH22 : ((Zlength (dist_before)) = 105)) (PreH23 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 v hd0 )
  **  (IntArray.undef_seg ( &( "head_" ) ) v (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "nxt_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "to_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd0: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (v > n_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= (n_pre + 1 ))) (PreH20 : ((Zlength (hd0)) = (v - 1 ))) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < (v - 1 ))) -> ((Znth j hd0 0) = (-1)))) (PreH22 : ((Zlength (dist_before)) = 105)) (PreH23 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 v hd0 )
  **  (IntArray.undef_seg ( &( "head_" ) ) v (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "nxt_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "to_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 goods 0)) /\ ((Znth i_2 goods 0) <= k_pre)))) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((((1 <= (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_3 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_3 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_3 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < m_pre)) -> (((Znth i_4 edge_u 0) = (fst ((Znth i_4 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_4 edge_v 0) = (snd ((Znth i_4 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : ((i < m_pre) -> ((((1 <= (Znth i edge_u 0)) /\ ((Znth i edge_u 0) <= n_pre)) /\ (1 <= (Znth i edge_v 0))) /\ ((Znth i edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i ))) (PreH23 : ((Zlength (tlst)) = (2 * i ))) (PreH24 : (AdjBuild n_pre i tree_edges hd nx tlst )) (PreH25 : (NxtRange i nx )) (PreH26 : (ArcToRange n_pre i tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  ((( &( "e" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (2 * i ) nx )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (2 * i ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 (2 * i ) tlst )
  **  (IntArray.undef_seg ( &( "to_" ) ) (2 * i ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ ((2 * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i )) ”
.

Definition solver_safety_wit_7 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd nx tlst )) (PreH25 : (NxtRange i_4 nx )) (PreH26 : (ArcToRange n_pre i_4 tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  ((( &( "e" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "i" ) )) # Int  |-> i_4)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (2 * i_4 ) nx )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (2 * i_4 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 (2 * i_4 ) tlst )
  **  (IntArray.undef_seg ( &( "to_" ) ) (2 * i_4 ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_8 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 goods 0)) /\ ((Znth i_2 goods 0) <= k_pre)))) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((((1 <= (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_3 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_3 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_3 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < m_pre)) -> (((Znth i_4 edge_u 0) = (fst ((Znth i_4 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_4 edge_v 0) = (snd ((Znth i_4 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : ((i < m_pre) -> ((((1 <= (Znth i edge_u 0)) /\ ((Znth i edge_u 0) <= n_pre)) /\ (1 <= (Znth i edge_v 0))) /\ ((Znth i edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i ))) (PreH23 : ((Zlength (tlst)) = (2 * i ))) (PreH24 : (AdjBuild n_pre i tree_edges hd nx tlst )) (PreH25 : (NxtRange i nx )) (PreH26 : (ArcToRange n_pre i tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i edge_u 0) - 1 )) ((2 * i )) (hd)) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 ((2 * i ) + 1 ) (app (nx) ((cons ((Znth ((Znth i edge_u 0) - 1 ) hd 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) ((2 * i ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 ((2 * i ) + 1 ) (app (tlst) ((cons ((Znth i edge_v 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) ((2 * i ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  ((( &( "e" ) )) # Int  |-> (2 * i ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (((2 * i ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * i ) + 1 )) ”
.

Definition solver_safety_wit_9 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd nx tlst )) (PreH25 : (NxtRange i_4 nx )) (PreH26 : (ArcToRange n_pre i_4 tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 ((2 * i_4 ) + 1 ) (app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 ((2 * i_4 ) + 1 ) (app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  ((( &( "e" ) )) # Int  |-> (2 * i_4 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "i" ) )) # Int  |-> i_4)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 goods 0)) /\ ((Znth i_2 goods 0) <= k_pre)))) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((((1 <= (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_3 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_3 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_3 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < m_pre)) -> (((Znth i_4 edge_u 0) = (fst ((Znth i_4 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_4 edge_v 0) = (snd ((Znth i_4 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : ((i < m_pre) -> ((((1 <= (Znth i edge_u 0)) /\ ((Znth i edge_u 0) <= n_pre)) /\ (1 <= (Znth i edge_v 0))) /\ ((Znth i edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i ))) (PreH23 : ((Zlength (tlst)) = (2 * i ))) (PreH24 : (AdjBuild n_pre i tree_edges hd nx tlst )) (PreH25 : (NxtRange i nx )) (PreH26 : (ArcToRange n_pre i tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg ( &( "to_" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app ((app (tlst) ((cons ((Znth i edge_v 0)) ((@nil Z)))))) ((cons ((Znth i edge_u 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) (((2 * i ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i edge_u 0) - 1 )) ((2 * i )) (hd)) )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 ((2 * i ) + 1 ) (app (nx) ((cons ((Znth ((Znth i edge_u 0) - 1 ) hd 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) ((2 * i ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  ((( &( "e" ) )) # Int  |-> (2 * i ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (((2 * i ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * i ) + 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd nx tlst )) (PreH25 : (NxtRange i_4 nx )) (PreH26 : (ArcToRange n_pre i_4 tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg ( &( "to_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z)))))) ((cons ((Znth i_4 edge_u 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 ((2 * i_4 ) + 1 ) (app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  ((( &( "e" ) )) # Int  |-> (2 * i_4 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "i" ) )) # Int  |-> i_4)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_12 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 goods 0)) /\ ((Znth i_2 goods 0) <= k_pre)))) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((((1 <= (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_3 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_3 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_3 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < m_pre)) -> (((Znth i_4 edge_u 0) = (fst ((Znth i_4 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_4 edge_v 0) = (snd ((Znth i_4 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : ((i < m_pre) -> ((((1 <= (Znth i edge_u 0)) /\ ((Znth i edge_u 0) <= n_pre)) /\ (1 <= (Znth i edge_v 0))) /\ ((Znth i edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i ))) (PreH23 : ((Zlength (tlst)) = (2 * i ))) (PreH24 : (AdjBuild n_pre i tree_edges hd nx tlst )) (PreH25 : (NxtRange i nx )) (PreH26 : (ArcToRange n_pre i tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app ((app (nx) ((cons ((Znth ((Znth i edge_u 0) - 1 ) hd 0)) ((@nil Z)))))) ((cons ((Znth ((Znth i edge_v 0) - 1 ) (replace_Znth (((Znth i edge_u 0) - 1 )) ((2 * i )) (hd)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (((2 * i ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i edge_u 0) - 1 )) ((2 * i )) (hd)) )
  **  (IntArray.seg ( &( "to_" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app ((app (tlst) ((cons ((Znth i edge_v 0)) ((@nil Z)))))) ((cons ((Znth i edge_u 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) (((2 * i ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  ((( &( "e" ) )) # Int  |-> (2 * i ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (((2 * i ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * i ) + 1 )) ”
.

Definition solver_safety_wit_13 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd nx tlst )) (PreH25 : (NxtRange i_4 nx )) (PreH26 : (ArcToRange n_pre i_4 tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z)))))) ((cons ((Znth ((Znth i_4 edge_v 0) - 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) )
  **  (IntArray.seg ( &( "to_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z)))))) ((cons ((Znth i_4 edge_u 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  ((( &( "e" ) )) # Int  |-> (2 * i_4 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "i" ) )) # Int  |-> i_4)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_14 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 goods 0)) /\ ((Znth i_2 goods 0) <= k_pre)))) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((((1 <= (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_3 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_3 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_3 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < m_pre)) -> (((Znth i_4 edge_u 0) = (fst ((Znth i_4 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_4 edge_v 0) = (snd ((Znth i_4 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i)) (PreH19 : (i <= m_pre)) (PreH20 : ((i < m_pre) -> ((((1 <= (Znth i edge_u 0)) /\ ((Znth i edge_u 0) <= n_pre)) /\ (1 <= (Znth i edge_v 0))) /\ ((Znth i edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i ))) (PreH23 : ((Zlength (tlst)) = (2 * i ))) (PreH24 : (AdjBuild n_pre i tree_edges hd nx tlst )) (PreH25 : (NxtRange i nx )) (PreH26 : (ArcToRange n_pre i tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i edge_v 0) - 1 )) (((2 * i ) + 1 )) ((replace_Znth (((Znth i edge_u 0) - 1 )) ((2 * i )) (hd)))) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app ((app (nx) ((cons ((Znth ((Znth i edge_u 0) - 1 ) hd 0)) ((@nil Z)))))) ((cons ((Znth ((Znth i edge_v 0) - 1 ) (replace_Znth (((Znth i edge_u 0) - 1 )) ((2 * i )) (hd)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (((2 * i ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 (((2 * i ) + 1 ) + 1 ) (app ((app (tlst) ((cons ((Znth i edge_v 0)) ((@nil Z)))))) ((cons ((Znth i edge_u 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) (((2 * i ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_15 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 >= m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd nx tlst )) (PreH25 : (NxtRange i_4 nx )) (PreH26 : (ArcToRange n_pre i_4 tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (2 * i_4 ) nx )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (2 * i_4 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 (2 * i_4 ) tlst )
  **  (IntArray.undef_seg ( &( "to_" ) ) (2 * i_4 ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_16 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd: (@list Z)) (nx: (@list Z)) (tlst: (@list Z)) (rows: (@list (@list Z))) (c: Z) (dist_after: (@list Z))  __default__List_Z  __default__Prod_Z_Z (PreH1 : ((Zlength (dist_after)) = 100005)) (PreH2 : (BfsRowResult n_pre tree_edges goods c dist_after )) (PreH3 : (Pre k_pre s_pre tree_edges goods )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (1 <= s_pre)) (PreH9 : (s_pre <= k_pre)) (PreH10 : (k_pre <= 100)) (PreH11 : (k_pre <= n_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH14 : (n_pre = (Zlength (goods)))) (PreH15 : (m_pre = (Zlength (tree_edges)))) (PreH16 : ((Zlength (edge_u)) = m_pre)) (PreH17 : ((Zlength (edge_v)) = m_pre)) (PreH18 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH19 : (1 <= c)) (PreH20 : (c <= k_pre)) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * m_pre ))) (PreH23 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH24 : (AdjBuild n_pre m_pre tree_edges hd nx tlst )) (PreH25 : (NxtRange m_pre nx )) (PreH26 : (ArcToRange n_pre m_pre tlst )) (PreH27 : ((Zlength (rows)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH29 : (BfsRows n_pre tree_edges goods rows c )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full ((( &( "dist_" ) ) + (c * (sizeof(INT) * 100005))) + (0 * sizeof(INT))) 100005 dist_after )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.missing_i ( &( "dist_" ) ) c 0 105 100005 rows )
|--
  “ ((c + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c + 1 )) ”
.

Definition solver_safety_wit_17 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd: (@list Z)) (nx: (@list Z)) (tlst: (@list Z)) (rows: (@list (@list Z))) (c: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (Pre k_pre s_pre tree_edges goods )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (1 <= s_pre)) (PreH7 : (s_pre <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (k_pre <= n_pre)) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH12 : (n_pre = (Zlength (goods)))) (PreH13 : (m_pre = (Zlength (tree_edges)))) (PreH14 : ((Zlength (edge_u)) = m_pre)) (PreH15 : ((Zlength (edge_v)) = m_pre)) (PreH16 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH17 : (1 <= c)) (PreH18 : (c <= k_pre)) (PreH19 : ((Zlength (hd)) = n_pre)) (PreH20 : ((Zlength (nx)) = (2 * m_pre ))) (PreH21 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH22 : (AdjBuild n_pre m_pre tree_edges hd nx tlst )) (PreH23 : (NxtRange m_pre nx )) (PreH24 : (ArcToRange n_pre m_pre tlst )) (PreH25 : ((Zlength (rows)) = 105)) (PreH26 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH27 : (BfsRows n_pre tree_edges goods rows c )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.missing_i ( &( "dist_" ) ) c 0 105 100005 rows )
  **  (IntArray.full ((( &( "dist_" ) ) + (c * (sizeof(INT) * 100005))) + (0 * sizeof(INT))) 100005 (Znth c rows __default__List_Z) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_18 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (rows: (@list (@list Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (c: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c > k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= c)) (PreH19 : (c <= (k_pre + 1 ))) (PreH20 : ((Zlength (hd)) = n_pre)) (PreH21 : ((Zlength (nx)) = (2 * m_pre ))) (PreH22 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH23 : (AdjBuild n_pre m_pre tree_edges hd nx tlst )) (PreH24 : (NxtRange m_pre nx )) (PreH25 : (ArcToRange n_pre m_pre tlst )) (PreH26 : ((Zlength (rows)) = 105)) (PreH27 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows c )) ,
  ((( &( "v" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_19 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (rows: (@list (@list Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (out: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (v > n_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (v = 1)) (PreH19 : ((Zlength (out)) = 0)) (PreH20 : ((Zlength (hd)) = n_pre)) (PreH21 : ((Zlength (nx)) = (2 * m_pre ))) (PreH22 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH23 : ((Zlength (rows)) = 105)) (PreH24 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH25 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH26 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  “ False ”
.

Definition solver_safety_wit_20 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (rows: (@list (@list Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (out: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (v = 1)) (PreH19 : ((Zlength (out)) = 0)) (PreH20 : ((Zlength (hd)) = n_pre)) (PreH21 : ((Zlength (nx)) = (2 * m_pre ))) (PreH22 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH23 : ((Zlength (rows)) = 105)) (PreH24 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH25 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH26 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) ,
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_21 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tmpl: (@list Z)) (rows: (@list (@list Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (out: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (2 <= v)) (PreH19 : (v <= (n_pre + 1 ))) (PreH20 : ((Zlength (out)) = (v - 1 ))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * m_pre ))) (PreH23 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH24 : ((Zlength (rows)) = 105)) (PreH25 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH26 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH27 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) (PreH28 : ((Zlength (tmpl)) = k_pre)) ,
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full ( &( "tmp_" ) ) k_pre tmpl )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_22 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tp: (@list Z)) (rows: (@list (@list Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (c: Z) (out: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c <= k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out)) = (v - 1 ))) (PreH21 : (1 <= c)) (PreH22 : (c <= (k_pre + 1 ))) (PreH23 : ((Zlength (hd)) = n_pre)) (PreH24 : ((Zlength (nx)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows)) = 105)) (PreH27 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) (PreH30 : ((Zlength (tp)) = (c - 1 ))) (PreH31 : (TmpPrefix n_pre tree_edges goods v tp (c - 1 ) )) ,
  (IntArray.seg ( &( "tmp_" ) ) 0 ((c - 1 ) + 1 ) (app (tp) ((cons ((Znth (v) ((Znth c rows __default__List_Z)) (0))) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "tmp_" ) ) ((c - 1 ) + 1 ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
|--
  “ ((c + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c + 1 )) ”
.

Definition solver_safety_wit_23 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tp: (@list Z)) (rows: (@list (@list Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (c: Z) (out: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c <= k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out)) = (v - 1 ))) (PreH21 : (1 <= c)) (PreH22 : (c <= (k_pre + 1 ))) (PreH23 : ((Zlength (hd)) = n_pre)) (PreH24 : ((Zlength (nx)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows)) = 105)) (PreH27 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) (PreH30 : ((Zlength (tp)) = (c - 1 ))) (PreH31 : (TmpPrefix n_pre tree_edges goods v tp (c - 1 ) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.seg ( &( "tmp_" ) ) 0 (c - 1 ) tp )
  **  (IntArray.undef_seg ( &( "tmp_" ) ) (c - 1 ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  “ ((c - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c - 1 )) ”
.

Definition solver_safety_wit_24 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tp: (@list Z)) (rows: (@list (@list Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (c: Z) (out: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c <= k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out)) = (v - 1 ))) (PreH21 : (1 <= c)) (PreH22 : (c <= (k_pre + 1 ))) (PreH23 : ((Zlength (hd)) = n_pre)) (PreH24 : ((Zlength (nx)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows)) = 105)) (PreH27 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) (PreH30 : ((Zlength (tp)) = (c - 1 ))) (PreH31 : (TmpPrefix n_pre tree_edges goods v tp (c - 1 ) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.seg ( &( "tmp_" ) ) 0 (c - 1 ) tp )
  **  (IntArray.undef_seg ( &( "tmp_" ) ) (c - 1 ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_25 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd: (@list Z)) (nx: (@list Z)) (tlst: (@list Z)) (rows: (@list (@list Z))) (out: (@list Z)) (tp: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (Pre k_pre s_pre tree_edges goods )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (1 <= s_pre)) (PreH7 : (s_pre <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (k_pre <= n_pre)) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH12 : (n_pre = (Zlength (goods)))) (PreH13 : (m_pre = (Zlength (tree_edges)))) (PreH14 : ((Zlength (edge_u)) = m_pre)) (PreH15 : ((Zlength (edge_v)) = m_pre)) (PreH16 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH17 : (1 <= v)) (PreH18 : (v <= n_pre)) (PreH19 : ((Zlength (out)) = (v - 1 ))) (PreH20 : ((Zlength (hd)) = n_pre)) (PreH21 : ((Zlength (nx)) = (2 * m_pre ))) (PreH22 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH23 : ((Zlength (rows)) = 105)) (PreH24 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH25 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH26 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) (PreH27 : (TmpPrefix n_pre tree_edges goods v tp k_pre )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full (( &( "tmp_" ) ) + (0 * sizeof(INT))) k_pre tp )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_26 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd: (@list Z)) (nx: (@list Z)) (tlst: (@list Z)) (rows: (@list (@list Z))) (out: (@list Z)) (tp: (@list Z)) (v: Z) (l1: (@list Z))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (Permutation tp l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (Pre k_pre s_pre tree_edges goods )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (1 <= s_pre)) (PreH9 : (s_pre <= k_pre)) (PreH10 : (k_pre <= 100)) (PreH11 : (k_pre <= n_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH14 : (n_pre = (Zlength (goods)))) (PreH15 : (m_pre = (Zlength (tree_edges)))) (PreH16 : ((Zlength (edge_u)) = m_pre)) (PreH17 : ((Zlength (edge_v)) = m_pre)) (PreH18 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH19 : (1 <= v)) (PreH20 : (v <= n_pre)) (PreH21 : ((Zlength (out)) = (v - 1 ))) (PreH22 : ((Zlength (hd)) = n_pre)) (PreH23 : ((Zlength (nx)) = (2 * m_pre ))) (PreH24 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH25 : ((Zlength (rows)) = 105)) (PreH26 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH27 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH28 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) (PreH29 : (TmpPrefix n_pre tree_edges goods v tp k_pre )) ,
  ((( &( "sum" ) )) # Int64  |->_)
  **  (IntArray.full (( &( "tmp_" ) ) + (0 * sizeof(INT))) k_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_27 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd: (@list Z)) (nx: (@list Z)) (tlst: (@list Z)) (rows: (@list (@list Z))) (out: (@list Z)) (tp: (@list Z)) (v: Z) (l1: (@list Z))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (Permutation tp l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (Pre k_pre s_pre tree_edges goods )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (1 <= s_pre)) (PreH9 : (s_pre <= k_pre)) (PreH10 : (k_pre <= 100)) (PreH11 : (k_pre <= n_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH14 : (n_pre = (Zlength (goods)))) (PreH15 : (m_pre = (Zlength (tree_edges)))) (PreH16 : ((Zlength (edge_u)) = m_pre)) (PreH17 : ((Zlength (edge_v)) = m_pre)) (PreH18 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH19 : (1 <= v)) (PreH20 : (v <= n_pre)) (PreH21 : ((Zlength (out)) = (v - 1 ))) (PreH22 : ((Zlength (hd)) = n_pre)) (PreH23 : ((Zlength (nx)) = (2 * m_pre ))) (PreH24 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH25 : ((Zlength (rows)) = 105)) (PreH26 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH27 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH28 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) (PreH29 : (TmpPrefix n_pre tree_edges goods v tp k_pre )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int64  |-> 0)
  **  (IntArray.full (( &( "tmp_" ) ) + (0 * sizeof(INT))) k_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_28 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (sum: Z) (tp0: (@list Z)) (l1: (@list Z)) (rows: (@list (@list Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i: Z) (out: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i < s_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 goods 0)) /\ ((Znth i_2 goods 0) <= k_pre)))) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((((1 <= (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_3 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_3 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_3 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < m_pre)) -> (((Znth i_4 edge_u 0) = (fst ((Znth i_4 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_4 edge_v 0) = (snd ((Znth i_4 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out)) = (v - 1 ))) (PreH21 : (0 <= i)) (PreH22 : (i <= s_pre)) (PreH23 : ((Zlength (hd)) = n_pre)) (PreH24 : ((Zlength (nx)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows)) = 105)) (PreH27 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) (PreH30 : ((Zlength (l1)) = k_pre)) (PreH31 : (mono_nondec l1 )) (PreH32 : ((Zlength (tp0)) = k_pre)) (PreH33 : (TmpPrefix n_pre tree_edges goods v tp0 k_pre )) (PreH34 : (Permutation tp0 l1 )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 ))))) (PreH36 : (sum = (ZSum ((sublist (0) (i) (l1)))))) ,
  (IntArray.full ( &( "tmp_" ) ) k_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int64  |-> (sum + (Znth i l1 0) ))
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_29 := 
(
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (sum: Z) (tp0: (@list Z)) (l1: (@list Z)) (rows: (@list (@list Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i: Z) (out: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i < s_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 goods 0)) /\ ((Znth i_2 goods 0) <= k_pre)))) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((((1 <= (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_3 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_3 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_3 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < m_pre)) -> (((Znth i_4 edge_u 0) = (fst ((Znth i_4 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_4 edge_v 0) = (snd ((Znth i_4 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out)) = (v - 1 ))) (PreH21 : (0 <= i)) (PreH22 : (i <= s_pre)) (PreH23 : ((Zlength (hd)) = n_pre)) (PreH24 : ((Zlength (nx)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows)) = 105)) (PreH27 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) (PreH30 : ((Zlength (l1)) = k_pre)) (PreH31 : (mono_nondec l1 )) (PreH32 : ((Zlength (tp0)) = k_pre)) (PreH33 : (TmpPrefix n_pre tree_edges goods v tp0 k_pre )) (PreH34 : (Permutation tp0 l1 )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 ))))) (PreH36 : (sum = (ZSum ((sublist (0) (i) (l1)))))) ,
  (IntArray.full ( &( "tmp_" ) ) k_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  “ ((sum + (Znth i l1 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (sum + (Znth i l1 0) )) ”
) \/
(
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (sum: Z) (tp0: (@list Z)) (l1: (@list Z)) (rows: (@list (@list Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i: Z) (out: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i < s_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 goods 0)) /\ ((Znth i_2 goods 0) <= k_pre)))) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((((1 <= (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_3 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_3 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_3 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < m_pre)) -> (((Znth i_4 edge_u 0) = (fst ((Znth i_4 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_4 edge_v 0) = (snd ((Znth i_4 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out)) = (v - 1 ))) (PreH21 : (0 <= i)) (PreH22 : (i <= s_pre)) (PreH23 : ((Zlength (hd)) = n_pre)) (PreH24 : ((Zlength (nx)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows)) = 105)) (PreH27 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) (PreH30 : ((Zlength (l1)) = k_pre)) (PreH31 : (mono_nondec l1 )) (PreH32 : ((Zlength (tp0)) = k_pre)) (PreH33 : (TmpPrefix n_pre tree_edges goods v tp0 k_pre )) (PreH34 : (Permutation tp0 l1 )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 ))))) (PreH36 : (sum = (ZSum ((sublist (0) (i) (l1)))))) ,
  (IntArray.full ( &( "tmp_" ) ) k_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  “ ((sum + (Znth i l1 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (sum + (Znth i l1 0) )) ”
).

Definition solver_safety_wit_29_split_goal_1 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (sum: Z) (tp0: (@list Z)) (l1: (@list Z)) (rows: (@list (@list Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i: Z) (out: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i < s_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 goods 0)) /\ ((Znth i_2 goods 0) <= k_pre)))) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((((1 <= (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_3 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_3 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_3 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < m_pre)) -> (((Znth i_4 edge_u 0) = (fst ((Znth i_4 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_4 edge_v 0) = (snd ((Znth i_4 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out)) = (v - 1 ))) (PreH21 : (0 <= i)) (PreH22 : (i <= s_pre)) (PreH23 : ((Zlength (hd)) = n_pre)) (PreH24 : ((Zlength (nx)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows)) = 105)) (PreH27 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) (PreH30 : ((Zlength (l1)) = k_pre)) (PreH31 : (mono_nondec l1 )) (PreH32 : ((Zlength (tp0)) = k_pre)) (PreH33 : (TmpPrefix n_pre tree_edges goods v tp0 k_pre )) (PreH34 : (Permutation tp0 l1 )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 ))))) (PreH36 : (sum = (ZSum ((sublist (0) (i) (l1)))))) ,
  (IntArray.full ( &( "tmp_" ) ) k_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  “ ((sum + (Znth i l1 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_29_split_goal_2 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (sum: Z) (tp0: (@list Z)) (l1: (@list Z)) (rows: (@list (@list Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i: Z) (out: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i < s_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((1 <= (Znth i_2 goods 0)) /\ ((Znth i_2 goods 0) <= k_pre)))) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((((1 <= (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_3 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_3 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_3 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < m_pre)) -> (((Znth i_4 edge_u 0) = (fst ((Znth i_4 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_4 edge_v 0) = (snd ((Znth i_4 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out)) = (v - 1 ))) (PreH21 : (0 <= i)) (PreH22 : (i <= s_pre)) (PreH23 : ((Zlength (hd)) = n_pre)) (PreH24 : ((Zlength (nx)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows)) = 105)) (PreH27 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) (PreH30 : ((Zlength (l1)) = k_pre)) (PreH31 : (mono_nondec l1 )) (PreH32 : ((Zlength (tp0)) = k_pre)) (PreH33 : (TmpPrefix n_pre tree_edges goods v tp0 k_pre )) (PreH34 : (Permutation tp0 l1 )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 ))))) (PreH36 : (sum = (ZSum ((sublist (0) (i) (l1)))))) ,
  (IntArray.full ( &( "tmp_" ) ) k_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  “ ((INT64_MIN) <= (sum + (Znth i l1 0) )) ”
.

Definition solver_safety_wit_30 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (sum: Z) (tp0: (@list Z)) (l1: (@list Z)) (rows: (@list (@list Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z) (out: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 >= s_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out)) = (v - 1 ))) (PreH21 : (0 <= i_4)) (PreH22 : (i_4 <= s_pre)) (PreH23 : ((Zlength (hd)) = n_pre)) (PreH24 : ((Zlength (nx)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows)) = 105)) (PreH27 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) (PreH30 : ((Zlength (l1)) = k_pre)) (PreH31 : (mono_nondec l1 )) (PreH32 : ((Zlength (tp0)) = k_pre)) (PreH33 : (TmpPrefix n_pre tree_edges goods v tp0 k_pre )) (PreH34 : (Permutation tp0 l1 )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 ))))) (PreH36 : (sum = (ZSum ((sublist (0) (i_4) (l1)))))) ,
  (Int64Array.seg cost_pre 1 (v + 1 ) (app (out) ((cons (sum) ((@nil Z))))) )
  **  (Int64Array.undef_seg cost_pre (v + 1 ) (n_pre + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full ( &( "tmp_" ) ) k_pre l1 )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  “ ((v + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (v + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (Pre k_pre s_pre tree_edges goods )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (1 <= s_pre)) (PreH7 : (s_pre <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (k_pre <= n_pre)) (PreH10 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH11 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < (Zlength (tree_edges)))) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH12 : (n_pre = (Zlength (goods)))) (PreH13 : (m_pre = (Zlength (tree_edges)))) (PreH14 : ((Zlength (edge_u)) = m_pre)) (PreH15 : ((Zlength (edge_v)) = m_pre)) (PreH16 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH17 : ((Zlength (dist_before)) = 105)) (PreH18 : forall (c: Z) , (((0 <= c) /\ (c < 105)) -> ((Zlength ((Znth c dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_seg ( &( "head_" ) ) 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "nxt_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "to_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  EX (hd0: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (hd0)) = (1 - 1 )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (1 - 1 ))) -> ((Znth j hd0 0) = (-1))) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 1 hd0 )
  **  (IntArray.undef_seg ( &( "head_" ) ) 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "nxt_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "to_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
) \/
(
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (Pre k_pre s_pre tree_edges goods )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (1 <= s_pre)) (PreH7 : (s_pre <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (k_pre <= n_pre)) (PreH10 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH11 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < (Zlength (tree_edges)))) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH12 : (n_pre = (Zlength (goods)))) (PreH13 : (m_pre = (Zlength (tree_edges)))) (PreH14 : ((Zlength (edge_u)) = m_pre)) (PreH15 : ((Zlength (edge_v)) = m_pre)) (PreH16 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH17 : ((Zlength (dist_before)) = 105)) (PreH18 : forall (c: Z) , (((0 <= c) /\ (c < 105)) -> ((Zlength ((Znth c dist_before __default__List_Z))) = 100005))) ,
  TT && emp 
|--
  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (1 - 1 ))) -> ((Znth j (@nil Z) 0) = (-1))) ” 
  &&  “ ((Zlength ((@nil Z))) = (1 - 1 )) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (Pre k_pre s_pre tree_edges goods )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (1 <= s_pre)) (PreH7 : (s_pre <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (k_pre <= n_pre)) (PreH10 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH11 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < (Zlength (tree_edges)))) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH12 : (n_pre = (Zlength (goods)))) (PreH13 : (m_pre = (Zlength (tree_edges)))) (PreH14 : ((Zlength (edge_u)) = m_pre)) (PreH15 : ((Zlength (edge_v)) = m_pre)) (PreH16 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH17 : ((Zlength (dist_before)) = 105)) (PreH18 : forall (c: Z) , (((0 <= c) /\ (c < 105)) -> ((Zlength ((Znth c dist_before __default__List_Z))) = 100005))) ,
  forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (Pre k_pre s_pre tree_edges goods )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (1 <= s_pre)) (PreH7 : (s_pre <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (k_pre <= n_pre)) (PreH10 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH11 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < (Zlength (tree_edges)))) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH12 : (n_pre = (Zlength (goods)))) (PreH13 : (m_pre = (Zlength (tree_edges)))) (PreH14 : ((Zlength (edge_u)) = m_pre)) (PreH15 : ((Zlength (edge_v)) = m_pre)) (PreH16 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH17 : ((Zlength (dist_before)) = 105)) (PreH18 : forall (c: Z) , (((0 <= c) /\ (c < 105)) -> ((Zlength ((Znth c dist_before __default__List_Z))) = 100005))) ,
  forall (j: Z) , (((0 <= j) /\ (j < (1 - 1 ))) -> ((Znth j (@nil Z) 0) = (-1)))
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (Pre k_pre s_pre tree_edges goods )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (1 <= s_pre)) (PreH7 : (s_pre <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (k_pre <= n_pre)) (PreH10 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH11 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < (Zlength (tree_edges)))) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH12 : (n_pre = (Zlength (goods)))) (PreH13 : (m_pre = (Zlength (tree_edges)))) (PreH14 : ((Zlength (edge_u)) = m_pre)) (PreH15 : ((Zlength (edge_v)) = m_pre)) (PreH16 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH17 : ((Zlength (dist_before)) = 105)) (PreH18 : forall (c: Z) , (((0 <= c) /\ (c < 105)) -> ((Zlength ((Znth c dist_before __default__List_Z))) = 100005))) ,
  ((Zlength ((@nil Z))) = (1 - 1 ))
.

Definition solver_entail_wit_1_split_goal_4 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (Pre k_pre s_pre tree_edges goods )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (1 <= s_pre)) (PreH7 : (s_pre <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (k_pre <= n_pre)) (PreH10 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH11 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < (Zlength (tree_edges)))) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH12 : (n_pre = (Zlength (goods)))) (PreH13 : (m_pre = (Zlength (tree_edges)))) (PreH14 : ((Zlength (edge_u)) = m_pre)) (PreH15 : ((Zlength (edge_v)) = m_pre)) (PreH16 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH17 : ((Zlength (dist_before)) = 105)) (PreH18 : forall (c: Z) , (((0 <= c) /\ (c < 105)) -> ((Zlength ((Znth c dist_before __default__List_Z))) = 100005))) ,
  forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_1_split_goal_5 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (Pre k_pre s_pre tree_edges goods )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (1 <= s_pre)) (PreH7 : (s_pre <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (k_pre <= n_pre)) (PreH10 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH11 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < (Zlength (tree_edges)))) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH12 : (n_pre = (Zlength (goods)))) (PreH13 : (m_pre = (Zlength (tree_edges)))) (PreH14 : ((Zlength (edge_u)) = m_pre)) (PreH15 : ((Zlength (edge_v)) = m_pre)) (PreH16 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH17 : ((Zlength (dist_before)) = 105)) (PreH18 : forall (c: Z) , (((0 <= c) /\ (c < 105)) -> ((Zlength ((Znth c dist_before __default__List_Z))) = 100005))) ,
  forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_1_split_goal_6 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (Pre k_pre s_pre tree_edges goods )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (1 <= s_pre)) (PreH7 : (s_pre <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (k_pre <= n_pre)) (PreH10 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH11 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < (Zlength (tree_edges)))) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH12 : (n_pre = (Zlength (goods)))) (PreH13 : (m_pre = (Zlength (tree_edges)))) (PreH14 : ((Zlength (edge_u)) = m_pre)) (PreH15 : ((Zlength (edge_v)) = m_pre)) (PreH16 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH17 : ((Zlength (dist_before)) = 105)) (PreH18 : forall (c: Z) , (((0 <= c) /\ (c < 105)) -> ((Zlength ((Znth c dist_before __default__List_Z))) = 100005))) ,
  forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))
.

Definition solver_entail_wit_2 := 
(
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd0_2: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= (n_pre + 1 ))) (PreH20 : ((Zlength (hd0_2)) = (v - 1 ))) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < (v - 1 ))) -> ((Znth j hd0_2 0) = (-1)))) (PreH22 : ((Zlength (dist_before)) = 105)) (PreH23 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg ( &( "head_" ) ) 1 (v + 1 ) (app (hd0_2) ((cons ((-1)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "head_" ) ) (v + 1 ) (n_pre + 1 ) )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "nxt_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "to_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  EX (hd0: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (hd0)) = ((v + 1 ) - 1 )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < ((v + 1 ) - 1 ))) -> ((Znth j hd0 0) = (-1))) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (v + 1 ) hd0 )
  **  (IntArray.undef_seg ( &( "head_" ) ) (v + 1 ) (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "nxt_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "to_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
) \/
(
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd0_2: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= (n_pre + 1 ))) (PreH20 : ((Zlength (hd0_2)) = (v - 1 ))) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < (v - 1 ))) -> ((Znth j hd0_2 0) = (-1)))) (PreH22 : ((Zlength (dist_before)) = 105)) (PreH23 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  TT && emp 
|--
  “ ((Zlength ((app (hd0_2) ((cons ((-1)) ((@nil Z))))))) = ((v + 1 ) - 1 )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd0_2: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= (n_pre + 1 ))) (PreH20 : ((Zlength (hd0_2)) = (v - 1 ))) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < (v - 1 ))) -> ((Znth j hd0_2 0) = (-1)))) (PreH22 : ((Zlength (dist_before)) = 105)) (PreH23 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  ((Zlength ((app (hd0_2) ((cons ((-1)) ((@nil Z))))))) = ((v + 1 ) - 1 ))
.

Definition solver_entail_wit_3 := 
(
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd0: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (v > n_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= (n_pre + 1 ))) (PreH20 : ((Zlength (hd0)) = (v - 1 ))) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < (v - 1 ))) -> ((Znth j hd0 0) = (-1)))) (PreH22 : ((Zlength (dist_before)) = 105)) (PreH23 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 v hd0 )
  **  (IntArray.undef_seg ( &( "head_" ) ) v (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "nxt_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "to_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  EX (tlst: (@list Z))  (nx: (@list Z))  (hd: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ ((0 < m_pre) -> ((((1 <= (Znth 0 edge_u 0)) /\ ((Znth 0 edge_u 0) <= n_pre)) /\ (1 <= (Znth 0 edge_v 0))) /\ ((Znth 0 edge_v 0) <= n_pre))) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * 0 )) ” 
  &&  “ ((Zlength (tlst)) = (2 * 0 )) ” 
  &&  “ (AdjBuild n_pre 0 tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange 0 nx ) ” 
  &&  “ (ArcToRange n_pre 0 tlst ) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (2 * 0 ) nx )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (2 * 0 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 (2 * 0 ) tlst )
  **  (IntArray.undef_seg ( &( "to_" ) ) (2 * 0 ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
) \/
(
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd0: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (v > n_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= (n_pre + 1 ))) (PreH20 : ((Zlength (hd0)) = (v - 1 ))) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < (v - 1 ))) -> ((Znth j hd0 0) = (-1)))) (PreH22 : ((Zlength (dist_before)) = 105)) (PreH23 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg ( &( "head_" ) ) 1 v hd0 )
  **  (IntArray.undef_full ( &( "nxt_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "to_" ) ) (2 * m_pre ) )
|--
  EX (tlst: (@list Z))  (nx: (@list Z))  (hd: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ ((0 < m_pre) -> ((((1 <= (Znth 0 edge_u 0)) /\ ((Znth 0 edge_u 0) <= n_pre)) /\ (1 <= (Znth 0 edge_v 0))) /\ ((Znth 0 edge_v 0) <= n_pre))) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * 0 )) ” 
  &&  “ ((Zlength (tlst)) = (2 * 0 )) ” 
  &&  “ (AdjBuild n_pre 0 tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange 0 nx ) ” 
  &&  “ (ArcToRange n_pre 0 tlst ) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (2 * 0 ) nx )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (2 * 0 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 (2 * 0 ) tlst )
  **  (IntArray.undef_seg ( &( "to_" ) ) (2 * 0 ) (2 * m_pre ) )
).

Definition solver_entail_wit_4 := 
(
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd_2)) = n_pre)) (PreH22 : ((Zlength (nx_2)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst_2)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd_2 nx_2 tlst_2 )) (PreH25 : (NxtRange i_4 nx_2 )) (PreH26 : (ArcToRange n_pre i_4 tlst_2 )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i_4 edge_v 0) - 1 )) (((2 * i_4 ) + 1 )) ((replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd_2)))) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (nx_2) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd_2 0)) ((@nil Z)))))) ((cons ((Znth ((Znth i_4 edge_v 0) - 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd_2)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (tlst_2) ((cons ((Znth i_4 edge_v 0)) ((@nil Z)))))) ((cons ((Znth i_4 edge_u 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  EX (tlst: (@list Z))  (nx: (@list Z))  (hd: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= (i_4 + 1 )) ” 
  &&  “ ((i_4 + 1 ) <= m_pre) ” 
  &&  “ (((i_4 + 1 ) < m_pre) -> ((((1 <= (Znth (i_4 + 1 ) edge_u 0)) /\ ((Znth (i_4 + 1 ) edge_u 0) <= n_pre)) /\ (1 <= (Znth (i_4 + 1 ) edge_v 0))) /\ ((Znth (i_4 + 1 ) edge_v 0) <= n_pre))) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * (i_4 + 1 ) )) ” 
  &&  “ ((Zlength (tlst)) = (2 * (i_4 + 1 ) )) ” 
  &&  “ (AdjBuild n_pre (i_4 + 1 ) tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange (i_4 + 1 ) nx ) ” 
  &&  “ (ArcToRange n_pre (i_4 + 1 ) tlst ) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (2 * (i_4 + 1 ) ) nx )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (2 * (i_4 + 1 ) ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 (2 * (i_4 + 1 ) ) tlst )
  **  (IntArray.undef_seg ( &( "to_" ) ) (2 * (i_4 + 1 ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
) \/
(
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd_2)) = n_pre)) (PreH22 : ((Zlength (nx_2)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst_2)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd_2 nx_2 tlst_2 )) (PreH25 : (NxtRange i_4 nx_2 )) (PreH26 : (ArcToRange n_pre i_4 tlst_2 )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg ( &( "nxt_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (nx_2) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd_2 0)) ((@nil Z)))))) ((cons ((Znth ((Znth i_4 edge_v 0) - 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd_2)) 0)) ((@nil Z))))) )
  **  (IntArray.seg ( &( "to_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (tlst_2) ((cons ((Znth i_4 edge_v 0)) ((@nil Z)))))) ((cons ((Znth i_4 edge_u 0)) ((@nil Z))))) )
|--
  EX (tlst: (@list Z))  (nx: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= (i_4 + 1 )) ” 
  &&  “ ((i_4 + 1 ) <= m_pre) ” 
  &&  “ (((i_4 + 1 ) < m_pre) -> ((((1 <= (Znth (i_4 + 1 ) edge_u 0)) /\ ((Znth (i_4 + 1 ) edge_u 0) <= n_pre)) /\ (1 <= (Znth (i_4 + 1 ) edge_v 0))) /\ ((Znth (i_4 + 1 ) edge_v 0) <= n_pre))) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth i_4 edge_v 0) - 1 )) (((2 * i_4 ) + 1 )) ((replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd_2)))))) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * (i_4 + 1 ) )) ” 
  &&  “ ((Zlength (tlst)) = (2 * (i_4 + 1 ) )) ” 
  &&  “ (AdjBuild n_pre (i_4 + 1 ) tree_edges (replace_Znth (((Znth i_4 edge_v 0) - 1 )) (((2 * i_4 ) + 1 )) ((replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd_2)))) nx tlst ) ” 
  &&  “ (NxtRange (i_4 + 1 ) nx ) ” 
  &&  “ (ArcToRange n_pre (i_4 + 1 ) tlst ) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (IntArray.seg ( &( "nxt_" ) ) 0 (2 * (i_4 + 1 ) ) nx )
  **  (IntArray.seg ( &( "to_" ) ) 0 (2 * (i_4 + 1 ) ) tlst )
).

Definition solver_entail_wit_5 := 
(
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (i_7: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_7 >= m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_7)) (PreH19 : (i_7 <= m_pre)) (PreH20 : ((i_7 < m_pre) -> ((((1 <= (Znth i_7 edge_u 0)) /\ ((Znth i_7 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_7 edge_v 0))) /\ ((Znth i_7 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd_2)) = n_pre)) (PreH22 : ((Zlength (nx_2)) = (2 * i_7 ))) (PreH23 : ((Zlength (tlst_2)) = (2 * i_7 ))) (PreH24 : (AdjBuild n_pre i_7 tree_edges hd_2 nx_2 tlst_2 )) (PreH25 : (NxtRange i_7 nx_2 )) (PreH26 : (ArcToRange n_pre i_7 tlst_2 )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd_2 )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (2 * i_7 ) nx_2 )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (2 * i_7 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 (2 * i_7 ) tlst_2 )
  **  (IntArray.undef_seg ( &( "to_" ) ) (2 * i_7 ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  EX (rows: (@list (@list Z)))  (tlst: (@list Z))  (nx: (@list Z))  (hd: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (k_pre + 1 )) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst)) = (2 * m_pre )) ” 
  &&  “ (AdjBuild n_pre m_pre tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange m_pre nx ) ” 
  &&  “ (ArcToRange n_pre m_pre tlst ) ” 
  &&  “ ((Zlength (rows)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows 1 ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
) \/
(
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (i_7: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_7 >= m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_7)) (PreH19 : (i_7 <= m_pre)) (PreH20 : ((i_7 < m_pre) -> ((((1 <= (Znth i_7 edge_u 0)) /\ ((Znth i_7 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_7 edge_v 0))) /\ ((Znth i_7 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd_2)) = n_pre)) (PreH22 : ((Zlength (nx_2)) = (2 * i_7 ))) (PreH23 : ((Zlength (tlst_2)) = (2 * i_7 ))) (PreH24 : (AdjBuild n_pre i_7 tree_edges hd_2 nx_2 tlst_2 )) (PreH25 : (NxtRange i_7 nx_2 )) (PreH26 : (ArcToRange n_pre i_7 tlst_2 )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 dist_before __default__List_Z))) = 100005))) ,
  TT && emp 
|--
  “ (BfsRows n_pre tree_edges goods dist_before 1 ) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ” 
  &&  “ (ArcToRange n_pre m_pre tlst_2 ) ” 
  &&  “ (NxtRange m_pre nx_2 ) ” 
  &&  “ (AdjBuild n_pre m_pre tree_edges hd_2 nx_2 tlst_2 ) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (i_7: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_7 >= m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_7)) (PreH19 : (i_7 <= m_pre)) (PreH20 : ((i_7 < m_pre) -> ((((1 <= (Znth i_7 edge_u 0)) /\ ((Znth i_7 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_7 edge_v 0))) /\ ((Znth i_7 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd_2)) = n_pre)) (PreH22 : ((Zlength (nx_2)) = (2 * i_7 ))) (PreH23 : ((Zlength (tlst_2)) = (2 * i_7 ))) (PreH24 : (AdjBuild n_pre i_7 tree_edges hd_2 nx_2 tlst_2 )) (PreH25 : (NxtRange i_7 nx_2 )) (PreH26 : (ArcToRange n_pre i_7 tlst_2 )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 dist_before __default__List_Z))) = 100005))) ,
  (BfsRows n_pre tree_edges goods dist_before 1 )
.

Definition solver_entail_wit_5_split_goal_2 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (i_7: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_7 >= m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_7)) (PreH19 : (i_7 <= m_pre)) (PreH20 : ((i_7 < m_pre) -> ((((1 <= (Znth i_7 edge_u 0)) /\ ((Znth i_7 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_7 edge_v 0))) /\ ((Znth i_7 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd_2)) = n_pre)) (PreH22 : ((Zlength (nx_2)) = (2 * i_7 ))) (PreH23 : ((Zlength (tlst_2)) = (2 * i_7 ))) (PreH24 : (AdjBuild n_pre i_7 tree_edges hd_2 nx_2 tlst_2 )) (PreH25 : (NxtRange i_7 nx_2 )) (PreH26 : (ArcToRange n_pre i_7 tlst_2 )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 dist_before __default__List_Z))) = 100005))) ,
  forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))
.

Definition solver_entail_wit_5_split_goal_3 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (i_7: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_7 >= m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_7)) (PreH19 : (i_7 <= m_pre)) (PreH20 : ((i_7 < m_pre) -> ((((1 <= (Znth i_7 edge_u 0)) /\ ((Znth i_7 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_7 edge_v 0))) /\ ((Znth i_7 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd_2)) = n_pre)) (PreH22 : ((Zlength (nx_2)) = (2 * i_7 ))) (PreH23 : ((Zlength (tlst_2)) = (2 * i_7 ))) (PreH24 : (AdjBuild n_pre i_7 tree_edges hd_2 nx_2 tlst_2 )) (PreH25 : (NxtRange i_7 nx_2 )) (PreH26 : (ArcToRange n_pre i_7 tlst_2 )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 dist_before __default__List_Z))) = 100005))) ,
  (ArcToRange n_pre m_pre tlst_2 )
.

Definition solver_entail_wit_5_split_goal_4 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (i_7: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_7 >= m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_7)) (PreH19 : (i_7 <= m_pre)) (PreH20 : ((i_7 < m_pre) -> ((((1 <= (Znth i_7 edge_u 0)) /\ ((Znth i_7 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_7 edge_v 0))) /\ ((Znth i_7 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd_2)) = n_pre)) (PreH22 : ((Zlength (nx_2)) = (2 * i_7 ))) (PreH23 : ((Zlength (tlst_2)) = (2 * i_7 ))) (PreH24 : (AdjBuild n_pre i_7 tree_edges hd_2 nx_2 tlst_2 )) (PreH25 : (NxtRange i_7 nx_2 )) (PreH26 : (ArcToRange n_pre i_7 tlst_2 )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 dist_before __default__List_Z))) = 100005))) ,
  (NxtRange m_pre nx_2 )
.

Definition solver_entail_wit_5_split_goal_5 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (i_7: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_7 >= m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_7)) (PreH19 : (i_7 <= m_pre)) (PreH20 : ((i_7 < m_pre) -> ((((1 <= (Znth i_7 edge_u 0)) /\ ((Znth i_7 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_7 edge_v 0))) /\ ((Znth i_7 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd_2)) = n_pre)) (PreH22 : ((Zlength (nx_2)) = (2 * i_7 ))) (PreH23 : ((Zlength (tlst_2)) = (2 * i_7 ))) (PreH24 : (AdjBuild n_pre i_7 tree_edges hd_2 nx_2 tlst_2 )) (PreH25 : (NxtRange i_7 nx_2 )) (PreH26 : (ArcToRange n_pre i_7 tlst_2 )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 dist_before __default__List_Z))) = 100005))) ,
  (AdjBuild n_pre m_pre tree_edges hd_2 nx_2 tlst_2 )
.

Definition solver_entail_wit_5_split_goal_6 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (i_7: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_7 >= m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_7)) (PreH19 : (i_7 <= m_pre)) (PreH20 : ((i_7 < m_pre) -> ((((1 <= (Znth i_7 edge_u 0)) /\ ((Znth i_7 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_7 edge_v 0))) /\ ((Znth i_7 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd_2)) = n_pre)) (PreH22 : ((Zlength (nx_2)) = (2 * i_7 ))) (PreH23 : ((Zlength (tlst_2)) = (2 * i_7 ))) (PreH24 : (AdjBuild n_pre i_7 tree_edges hd_2 nx_2 tlst_2 )) (PreH25 : (NxtRange i_7 nx_2 )) (PreH26 : (ArcToRange n_pre i_7 tlst_2 )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 dist_before __default__List_Z))) = 100005))) ,
  forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_5_split_goal_7 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (i_7: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_7 >= m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_7)) (PreH19 : (i_7 <= m_pre)) (PreH20 : ((i_7 < m_pre) -> ((((1 <= (Znth i_7 edge_u 0)) /\ ((Znth i_7 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_7 edge_v 0))) /\ ((Znth i_7 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd_2)) = n_pre)) (PreH22 : ((Zlength (nx_2)) = (2 * i_7 ))) (PreH23 : ((Zlength (tlst_2)) = (2 * i_7 ))) (PreH24 : (AdjBuild n_pre i_7 tree_edges hd_2 nx_2 tlst_2 )) (PreH25 : (NxtRange i_7 nx_2 )) (PreH26 : (ArcToRange n_pre i_7 tlst_2 )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 dist_before __default__List_Z))) = 100005))) ,
  forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_5_split_goal_8 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (i_7: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_7 >= m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_7)) (PreH19 : (i_7 <= m_pre)) (PreH20 : ((i_7 < m_pre) -> ((((1 <= (Znth i_7 edge_u 0)) /\ ((Znth i_7 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_7 edge_v 0))) /\ ((Znth i_7 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd_2)) = n_pre)) (PreH22 : ((Zlength (nx_2)) = (2 * i_7 ))) (PreH23 : ((Zlength (tlst_2)) = (2 * i_7 ))) (PreH24 : (AdjBuild n_pre i_7 tree_edges hd_2 nx_2 tlst_2 )) (PreH25 : (NxtRange i_7 nx_2 )) (PreH26 : (ArcToRange n_pre i_7 tlst_2 )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 dist_before __default__List_Z))) = 100005))) ,
  forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))
.

Definition solver_entail_wit_6 := 
(
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (rows_2: (@list (@list Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (c: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c <= k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= c)) (PreH19 : (c <= (k_pre + 1 ))) (PreH20 : ((Zlength (hd_2)) = n_pre)) (PreH21 : ((Zlength (nx_2)) = (2 * m_pre ))) (PreH22 : ((Zlength (tlst_2)) = (2 * m_pre ))) (PreH23 : (AdjBuild n_pre m_pre tree_edges hd_2 nx_2 tlst_2 )) (PreH24 : (NxtRange m_pre nx_2 )) (PreH25 : (ArcToRange n_pre m_pre tlst_2 )) (PreH26 : ((Zlength (rows_2)) = 105)) (PreH27 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 rows_2 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_2 c )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd_2 )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx_2 )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst_2 )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows_2 )
|--
  EX (rows: (@list (@list Z)))  (tlst: (@list Z))  (nx: (@list Z))  (hd: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= c) ” 
  &&  “ (c <= k_pre) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst)) = (2 * m_pre )) ” 
  &&  “ (AdjBuild n_pre m_pre tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange m_pre nx ) ” 
  &&  “ (ArcToRange n_pre m_pre tlst ) ” 
  &&  “ ((Zlength (rows)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows c ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.missing_i ( &( "dist_" ) ) c 0 105 100005 rows )
  **  (IntArray.full ((( &( "dist_" ) ) + (c * (sizeof(INT) * 100005))) + (0 * sizeof(INT))) 100005 (Znth c rows __default__List_Z) )
) \/
(
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (rows_2: (@list (@list Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (c: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c <= k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= c)) (PreH19 : (c <= (k_pre + 1 ))) (PreH20 : ((Zlength (hd_2)) = n_pre)) (PreH21 : ((Zlength (nx_2)) = (2 * m_pre ))) (PreH22 : ((Zlength (tlst_2)) = (2 * m_pre ))) (PreH23 : (AdjBuild n_pre m_pre tree_edges hd_2 nx_2 tlst_2 )) (PreH24 : (NxtRange m_pre nx_2 )) (PreH25 : (ArcToRange n_pre m_pre tlst_2 )) (PreH26 : ((Zlength (rows_2)) = 105)) (PreH27 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 rows_2 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_2 c )) ,
  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= c) ” 
  &&  “ (c <= k_pre) ” 
  &&  “ ((Zlength (hd_2)) = n_pre) ” 
  &&  “ ((Zlength (nx_2)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst_2)) = (2 * m_pre )) ” 
  &&  “ (AdjBuild n_pre m_pre tree_edges hd_2 nx_2 tlst_2 ) ” 
  &&  “ (NxtRange m_pre nx_2 ) ” 
  &&  “ (ArcToRange n_pre m_pre tlst_2 ) ” 
  &&  “ ((Zlength (rows)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows c ) ”
  &&  (IntArray2.missing_i ( &( "dist_" ) ) c 0 105 100005 rows )
  **  (IntArray.full ((( &( "dist_" ) ) + (c * (sizeof(INT) * 100005))) + (0 * sizeof(INT))) 100005 (Znth c rows __default__List_Z) )
).

Definition solver_entail_wit_7 := 
(
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd_2: (@list Z)) (nx_2: (@list Z)) (tlst_2: (@list Z)) (rows_2: (@list (@list Z))) (c: Z) (dist_after: (@list Z))  __default__List_Z  __default__Prod_Z_Z (PreH1 : ((Zlength (dist_after)) = 100005)) (PreH2 : (BfsRowResult n_pre tree_edges goods c dist_after )) (PreH3 : (Pre k_pre s_pre tree_edges goods )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (1 <= s_pre)) (PreH9 : (s_pre <= k_pre)) (PreH10 : (k_pre <= 100)) (PreH11 : (k_pre <= n_pre)) (PreH12 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH13 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH14 : (n_pre = (Zlength (goods)))) (PreH15 : (m_pre = (Zlength (tree_edges)))) (PreH16 : ((Zlength (edge_u)) = m_pre)) (PreH17 : ((Zlength (edge_v)) = m_pre)) (PreH18 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH19 : (1 <= c)) (PreH20 : (c <= k_pre)) (PreH21 : ((Zlength (hd_2)) = n_pre)) (PreH22 : ((Zlength (nx_2)) = (2 * m_pre ))) (PreH23 : ((Zlength (tlst_2)) = (2 * m_pre ))) (PreH24 : (AdjBuild n_pre m_pre tree_edges hd_2 nx_2 tlst_2 )) (PreH25 : (NxtRange m_pre nx_2 )) (PreH26 : (ArcToRange n_pre m_pre tlst_2 )) (PreH27 : ((Zlength (rows_2)) = 105)) (PreH28 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 rows_2 __default__List_Z))) = 100005))) (PreH29 : (BfsRows n_pre tree_edges goods rows_2 c )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd_2 )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx_2 )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst_2 )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full ((( &( "dist_" ) ) + (c * (sizeof(INT) * 100005))) + (0 * sizeof(INT))) 100005 dist_after )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.missing_i ( &( "dist_" ) ) c 0 105 100005 rows_2 )
|--
  EX (rows: (@list (@list Z)))  (tlst: (@list Z))  (nx: (@list Z))  (hd: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= (c + 1 )) ” 
  &&  “ ((c + 1 ) <= (k_pre + 1 )) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst)) = (2 * m_pre )) ” 
  &&  “ (AdjBuild n_pre m_pre tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange m_pre nx ) ” 
  &&  “ (ArcToRange n_pre m_pre tlst ) ” 
  &&  “ ((Zlength (rows)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows (c + 1 ) ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
) \/
(
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd_2: (@list Z)) (nx_2: (@list Z)) (tlst_2: (@list Z)) (rows_2: (@list (@list Z))) (c: Z) (dist_after: (@list Z))  __default__List_Z  __default__Prod_Z_Z (PreH1 : ((Zlength (dist_after)) = 100005)) (PreH2 : (BfsRowResult n_pre tree_edges goods c dist_after )) (PreH3 : (Pre k_pre s_pre tree_edges goods )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (1 <= s_pre)) (PreH9 : (s_pre <= k_pre)) (PreH10 : (k_pre <= 100)) (PreH11 : (k_pre <= n_pre)) (PreH12 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH13 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH14 : (n_pre = (Zlength (goods)))) (PreH15 : (m_pre = (Zlength (tree_edges)))) (PreH16 : ((Zlength (edge_u)) = m_pre)) (PreH17 : ((Zlength (edge_v)) = m_pre)) (PreH18 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH19 : (1 <= c)) (PreH20 : (c <= k_pre)) (PreH21 : ((Zlength (hd_2)) = n_pre)) (PreH22 : ((Zlength (nx_2)) = (2 * m_pre ))) (PreH23 : ((Zlength (tlst_2)) = (2 * m_pre ))) (PreH24 : (AdjBuild n_pre m_pre tree_edges hd_2 nx_2 tlst_2 )) (PreH25 : (NxtRange m_pre nx_2 )) (PreH26 : (ArcToRange n_pre m_pre tlst_2 )) (PreH27 : ((Zlength (rows_2)) = 105)) (PreH28 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 rows_2 __default__List_Z))) = 100005))) (PreH29 : (BfsRows n_pre tree_edges goods rows_2 c )) ,
  (IntArray.full ((( &( "dist_" ) ) + (c * (sizeof(INT) * 100005))) + (0 * sizeof(INT))) 100005 dist_after )
  **  (IntArray2.missing_i ( &( "dist_" ) ) c 0 105 100005 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= (c + 1 )) ” 
  &&  “ ((c + 1 ) <= (k_pre + 1 )) ” 
  &&  “ ((Zlength (hd_2)) = n_pre) ” 
  &&  “ ((Zlength (nx_2)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst_2)) = (2 * m_pre )) ” 
  &&  “ (AdjBuild n_pre m_pre tree_edges hd_2 nx_2 tlst_2 ) ” 
  &&  “ (NxtRange m_pre nx_2 ) ” 
  &&  “ (ArcToRange n_pre m_pre tlst_2 ) ” 
  &&  “ ((Zlength (rows)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows (c + 1 ) ) ”
  &&  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
).

Definition solver_entail_wit_8 := 
(
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (rows_3: (@list (@list Z))) (tlst_3: (@list Z)) (nx_3: (@list Z)) (hd_3: (@list Z)) (c: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c > k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_7: Z) , (((0 <= i_7) /\ (i_7 < n_pre)) -> ((1 <= (Znth i_7 goods 0)) /\ ((Znth i_7 goods 0) <= k_pre)))) (PreH12 : forall (i_8: Z) , (((0 <= i_8) /\ (i_8 < m_pre)) -> (((((1 <= (fst ((Znth i_8 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_9: Z) , (((0 <= i_9) /\ (i_9 < m_pre)) -> (((Znth i_9 edge_u 0) = (fst ((Znth i_9 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_9 edge_v 0) = (snd ((Znth i_9 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= c)) (PreH19 : (c <= (k_pre + 1 ))) (PreH20 : ((Zlength (hd_3)) = n_pre)) (PreH21 : ((Zlength (nx_3)) = (2 * m_pre ))) (PreH22 : ((Zlength (tlst_3)) = (2 * m_pre ))) (PreH23 : (AdjBuild n_pre m_pre tree_edges hd_3 nx_3 tlst_3 )) (PreH24 : (NxtRange m_pre nx_3 )) (PreH25 : (ArcToRange n_pre m_pre tlst_3 )) (PreH26 : ((Zlength (rows_3)) = 105)) (PreH27 : forall (cc_3: Z) , (((0 <= cc_3) /\ (cc_3 < 105)) -> ((Zlength ((Znth cc_3 rows_3 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_3 c )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd_3 )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx_3 )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst_3 )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows_3 )
|--
  EX (rows: (@list (@list Z)))  (tlst: (@list Z))  (nx: (@list Z))  (hd: (@list Z))  (out: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 = 1) ” 
  &&  “ ((Zlength (out)) = 0) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (rows)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) ) ” 
  &&  “ (OutPrefix n_pre s_pre tree_edges goods out (1 - 1 ) ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 1 out )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
) \/
(
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (rows_3: (@list (@list Z))) (tlst_3: (@list Z)) (nx_3: (@list Z)) (hd_3: (@list Z)) (c: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c > k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_7: Z) , (((0 <= i_7) /\ (i_7 < n_pre)) -> ((1 <= (Znth i_7 goods 0)) /\ ((Znth i_7 goods 0) <= k_pre)))) (PreH12 : forall (i_8: Z) , (((0 <= i_8) /\ (i_8 < m_pre)) -> (((((1 <= (fst ((Znth i_8 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_9: Z) , (((0 <= i_9) /\ (i_9 < m_pre)) -> (((Znth i_9 edge_u 0) = (fst ((Znth i_9 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_9 edge_v 0) = (snd ((Znth i_9 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= c)) (PreH19 : (c <= (k_pre + 1 ))) (PreH20 : ((Zlength (hd_3)) = n_pre)) (PreH21 : ((Zlength (nx_3)) = (2 * m_pre ))) (PreH22 : ((Zlength (tlst_3)) = (2 * m_pre ))) (PreH23 : (AdjBuild n_pre m_pre tree_edges hd_3 nx_3 tlst_3 )) (PreH24 : (NxtRange m_pre nx_3 )) (PreH25 : (ArcToRange n_pre m_pre tlst_3 )) (PreH26 : ((Zlength (rows_3)) = 105)) (PreH27 : forall (cc_3: Z) , (((0 <= cc_3) /\ (cc_3 < 105)) -> ((Zlength ((Znth cc_3 rows_3 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_3 c )) ,
  TT && emp 
|--
  “ (OutPrefix n_pre s_pre tree_edges goods (@nil Z) (1 - 1 ) ) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows_3 (k_pre + 1 ) ) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows_3 __default__List_Z))) = 100005)) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ”
  &&  emp
).

Definition solver_entail_wit_8_split_goal_1 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (rows_3: (@list (@list Z))) (tlst_3: (@list Z)) (nx_3: (@list Z)) (hd_3: (@list Z)) (c: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c > k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_7: Z) , (((0 <= i_7) /\ (i_7 < n_pre)) -> ((1 <= (Znth i_7 goods 0)) /\ ((Znth i_7 goods 0) <= k_pre)))) (PreH12 : forall (i_8: Z) , (((0 <= i_8) /\ (i_8 < m_pre)) -> (((((1 <= (fst ((Znth i_8 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_9: Z) , (((0 <= i_9) /\ (i_9 < m_pre)) -> (((Znth i_9 edge_u 0) = (fst ((Znth i_9 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_9 edge_v 0) = (snd ((Znth i_9 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= c)) (PreH19 : (c <= (k_pre + 1 ))) (PreH20 : ((Zlength (hd_3)) = n_pre)) (PreH21 : ((Zlength (nx_3)) = (2 * m_pre ))) (PreH22 : ((Zlength (tlst_3)) = (2 * m_pre ))) (PreH23 : (AdjBuild n_pre m_pre tree_edges hd_3 nx_3 tlst_3 )) (PreH24 : (NxtRange m_pre nx_3 )) (PreH25 : (ArcToRange n_pre m_pre tlst_3 )) (PreH26 : ((Zlength (rows_3)) = 105)) (PreH27 : forall (cc_3: Z) , (((0 <= cc_3) /\ (cc_3 < 105)) -> ((Zlength ((Znth cc_3 rows_3 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_3 c )) ,
  (OutPrefix n_pre s_pre tree_edges goods (@nil Z) (1 - 1 ) )
.

Definition solver_entail_wit_8_split_goal_2 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (rows_3: (@list (@list Z))) (tlst_3: (@list Z)) (nx_3: (@list Z)) (hd_3: (@list Z)) (c: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c > k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_7: Z) , (((0 <= i_7) /\ (i_7 < n_pre)) -> ((1 <= (Znth i_7 goods 0)) /\ ((Znth i_7 goods 0) <= k_pre)))) (PreH12 : forall (i_8: Z) , (((0 <= i_8) /\ (i_8 < m_pre)) -> (((((1 <= (fst ((Znth i_8 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_9: Z) , (((0 <= i_9) /\ (i_9 < m_pre)) -> (((Znth i_9 edge_u 0) = (fst ((Znth i_9 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_9 edge_v 0) = (snd ((Znth i_9 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= c)) (PreH19 : (c <= (k_pre + 1 ))) (PreH20 : ((Zlength (hd_3)) = n_pre)) (PreH21 : ((Zlength (nx_3)) = (2 * m_pre ))) (PreH22 : ((Zlength (tlst_3)) = (2 * m_pre ))) (PreH23 : (AdjBuild n_pre m_pre tree_edges hd_3 nx_3 tlst_3 )) (PreH24 : (NxtRange m_pre nx_3 )) (PreH25 : (ArcToRange n_pre m_pre tlst_3 )) (PreH26 : ((Zlength (rows_3)) = 105)) (PreH27 : forall (cc_3: Z) , (((0 <= cc_3) /\ (cc_3 < 105)) -> ((Zlength ((Znth cc_3 rows_3 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_3 c )) ,
  (BfsRows n_pre tree_edges goods rows_3 (k_pre + 1 ) )
.

Definition solver_entail_wit_8_split_goal_3 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (rows_3: (@list (@list Z))) (tlst_3: (@list Z)) (nx_3: (@list Z)) (hd_3: (@list Z)) (c: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c > k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_7: Z) , (((0 <= i_7) /\ (i_7 < n_pre)) -> ((1 <= (Znth i_7 goods 0)) /\ ((Znth i_7 goods 0) <= k_pre)))) (PreH12 : forall (i_8: Z) , (((0 <= i_8) /\ (i_8 < m_pre)) -> (((((1 <= (fst ((Znth i_8 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_9: Z) , (((0 <= i_9) /\ (i_9 < m_pre)) -> (((Znth i_9 edge_u 0) = (fst ((Znth i_9 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_9 edge_v 0) = (snd ((Znth i_9 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= c)) (PreH19 : (c <= (k_pre + 1 ))) (PreH20 : ((Zlength (hd_3)) = n_pre)) (PreH21 : ((Zlength (nx_3)) = (2 * m_pre ))) (PreH22 : ((Zlength (tlst_3)) = (2 * m_pre ))) (PreH23 : (AdjBuild n_pre m_pre tree_edges hd_3 nx_3 tlst_3 )) (PreH24 : (NxtRange m_pre nx_3 )) (PreH25 : (ArcToRange n_pre m_pre tlst_3 )) (PreH26 : ((Zlength (rows_3)) = 105)) (PreH27 : forall (cc_3: Z) , (((0 <= cc_3) /\ (cc_3 < 105)) -> ((Zlength ((Znth cc_3 rows_3 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_3 c )) ,
  forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows_3 __default__List_Z))) = 100005))
.

Definition solver_entail_wit_8_split_goal_4 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (rows_3: (@list (@list Z))) (tlst_3: (@list Z)) (nx_3: (@list Z)) (hd_3: (@list Z)) (c: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c > k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_7: Z) , (((0 <= i_7) /\ (i_7 < n_pre)) -> ((1 <= (Znth i_7 goods 0)) /\ ((Znth i_7 goods 0) <= k_pre)))) (PreH12 : forall (i_8: Z) , (((0 <= i_8) /\ (i_8 < m_pre)) -> (((((1 <= (fst ((Znth i_8 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_9: Z) , (((0 <= i_9) /\ (i_9 < m_pre)) -> (((Znth i_9 edge_u 0) = (fst ((Znth i_9 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_9 edge_v 0) = (snd ((Znth i_9 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= c)) (PreH19 : (c <= (k_pre + 1 ))) (PreH20 : ((Zlength (hd_3)) = n_pre)) (PreH21 : ((Zlength (nx_3)) = (2 * m_pre ))) (PreH22 : ((Zlength (tlst_3)) = (2 * m_pre ))) (PreH23 : (AdjBuild n_pre m_pre tree_edges hd_3 nx_3 tlst_3 )) (PreH24 : (NxtRange m_pre nx_3 )) (PreH25 : (ArcToRange n_pre m_pre tlst_3 )) (PreH26 : ((Zlength (rows_3)) = 105)) (PreH27 : forall (cc_3: Z) , (((0 <= cc_3) /\ (cc_3 < 105)) -> ((Zlength ((Znth cc_3 rows_3 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_3 c )) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition solver_entail_wit_8_split_goal_5 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (rows_3: (@list (@list Z))) (tlst_3: (@list Z)) (nx_3: (@list Z)) (hd_3: (@list Z)) (c: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c > k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_7: Z) , (((0 <= i_7) /\ (i_7 < n_pre)) -> ((1 <= (Znth i_7 goods 0)) /\ ((Znth i_7 goods 0) <= k_pre)))) (PreH12 : forall (i_8: Z) , (((0 <= i_8) /\ (i_8 < m_pre)) -> (((((1 <= (fst ((Znth i_8 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_9: Z) , (((0 <= i_9) /\ (i_9 < m_pre)) -> (((Znth i_9 edge_u 0) = (fst ((Znth i_9 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_9 edge_v 0) = (snd ((Znth i_9 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= c)) (PreH19 : (c <= (k_pre + 1 ))) (PreH20 : ((Zlength (hd_3)) = n_pre)) (PreH21 : ((Zlength (nx_3)) = (2 * m_pre ))) (PreH22 : ((Zlength (tlst_3)) = (2 * m_pre ))) (PreH23 : (AdjBuild n_pre m_pre tree_edges hd_3 nx_3 tlst_3 )) (PreH24 : (NxtRange m_pre nx_3 )) (PreH25 : (ArcToRange n_pre m_pre tlst_3 )) (PreH26 : ((Zlength (rows_3)) = 105)) (PreH27 : forall (cc_3: Z) , (((0 <= cc_3) /\ (cc_3 < 105)) -> ((Zlength ((Znth cc_3 rows_3 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_3 c )) ,
  forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_8_split_goal_6 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (rows_3: (@list (@list Z))) (tlst_3: (@list Z)) (nx_3: (@list Z)) (hd_3: (@list Z)) (c: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c > k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_7: Z) , (((0 <= i_7) /\ (i_7 < n_pre)) -> ((1 <= (Znth i_7 goods 0)) /\ ((Znth i_7 goods 0) <= k_pre)))) (PreH12 : forall (i_8: Z) , (((0 <= i_8) /\ (i_8 < m_pre)) -> (((((1 <= (fst ((Znth i_8 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_9: Z) , (((0 <= i_9) /\ (i_9 < m_pre)) -> (((Znth i_9 edge_u 0) = (fst ((Znth i_9 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_9 edge_v 0) = (snd ((Znth i_9 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= c)) (PreH19 : (c <= (k_pre + 1 ))) (PreH20 : ((Zlength (hd_3)) = n_pre)) (PreH21 : ((Zlength (nx_3)) = (2 * m_pre ))) (PreH22 : ((Zlength (tlst_3)) = (2 * m_pre ))) (PreH23 : (AdjBuild n_pre m_pre tree_edges hd_3 nx_3 tlst_3 )) (PreH24 : (NxtRange m_pre nx_3 )) (PreH25 : (ArcToRange n_pre m_pre tlst_3 )) (PreH26 : ((Zlength (rows_3)) = 105)) (PreH27 : forall (cc_3: Z) , (((0 <= cc_3) /\ (cc_3 < 105)) -> ((Zlength ((Znth cc_3 rows_3 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_3 c )) ,
  forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_8_split_goal_7 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (rows_3: (@list (@list Z))) (tlst_3: (@list Z)) (nx_3: (@list Z)) (hd_3: (@list Z)) (c: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c > k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_7: Z) , (((0 <= i_7) /\ (i_7 < n_pre)) -> ((1 <= (Znth i_7 goods 0)) /\ ((Znth i_7 goods 0) <= k_pre)))) (PreH12 : forall (i_8: Z) , (((0 <= i_8) /\ (i_8 < m_pre)) -> (((((1 <= (fst ((Znth i_8 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_9: Z) , (((0 <= i_9) /\ (i_9 < m_pre)) -> (((Znth i_9 edge_u 0) = (fst ((Znth i_9 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_9 edge_v 0) = (snd ((Znth i_9 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= c)) (PreH19 : (c <= (k_pre + 1 ))) (PreH20 : ((Zlength (hd_3)) = n_pre)) (PreH21 : ((Zlength (nx_3)) = (2 * m_pre ))) (PreH22 : ((Zlength (tlst_3)) = (2 * m_pre ))) (PreH23 : (AdjBuild n_pre m_pre tree_edges hd_3 nx_3 tlst_3 )) (PreH24 : (NxtRange m_pre nx_3 )) (PreH25 : (ArcToRange n_pre m_pre tlst_3 )) (PreH26 : ((Zlength (rows_3)) = 105)) (PreH27 : forall (cc_3: Z) , (((0 <= cc_3) /\ (cc_3 < 105)) -> ((Zlength ((Znth cc_3 rows_3 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_3 c )) ,
  forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))
.

Definition solver_entail_wit_9_1 := 
(
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (rows_2: (@list (@list Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (out_2: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (v = 1)) (PreH19 : ((Zlength (out_2)) = 0)) (PreH20 : ((Zlength (hd_2)) = n_pre)) (PreH21 : ((Zlength (nx_2)) = (2 * m_pre ))) (PreH22 : ((Zlength (tlst_2)) = (2 * m_pre ))) (PreH23 : ((Zlength (rows_2)) = 105)) (PreH24 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 rows_2 __default__List_Z))) = 100005))) (PreH25 : (BfsRows n_pre tree_edges goods rows_2 (k_pre + 1 ) )) (PreH26 : (OutPrefix n_pre s_pre tree_edges goods out_2 (v - 1 ) )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out_2 )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd_2 )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx_2 )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst_2 )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows_2 )
|--
  EX (tp: (@list Z))  (rows: (@list (@list Z)))  (tlst: (@list Z))  (nx: (@list Z))  (hd: (@list Z))  (out: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ ((Zlength (out)) = (v - 1 )) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (k_pre + 1 )) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (rows)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) ) ” 
  &&  “ (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) ) ” 
  &&  “ ((Zlength (tp)) = (1 - 1 )) ” 
  &&  “ (TmpPrefix n_pre tree_edges goods v tp (1 - 1 ) ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.seg ( &( "tmp_" ) ) 0 (1 - 1 ) tp )
  **  (IntArray.undef_seg ( &( "tmp_" ) ) (1 - 1 ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
) \/
(
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (rows_2: (@list (@list Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (out_2: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (v = 1)) (PreH19 : ((Zlength (out_2)) = 0)) (PreH20 : ((Zlength (hd_2)) = n_pre)) (PreH21 : ((Zlength (nx_2)) = (2 * m_pre ))) (PreH22 : ((Zlength (tlst_2)) = (2 * m_pre ))) (PreH23 : ((Zlength (rows_2)) = 105)) (PreH24 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 rows_2 __default__List_Z))) = 100005))) (PreH25 : (BfsRows n_pre tree_edges goods rows_2 (k_pre + 1 ) )) (PreH26 : (OutPrefix n_pre s_pre tree_edges goods out_2 (v - 1 ) )) ,
  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
|--
  EX (tp: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ ((Zlength (out_2)) = (v - 1 )) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (k_pre + 1 )) ” 
  &&  “ ((Zlength (hd_2)) = n_pre) ” 
  &&  “ ((Zlength (nx_2)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst_2)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (rows_2)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows_2 __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows_2 (k_pre + 1 ) ) ” 
  &&  “ (OutPrefix n_pre s_pre tree_edges goods out_2 (v - 1 ) ) ” 
  &&  “ ((Zlength (tp)) = (1 - 1 )) ” 
  &&  “ (TmpPrefix n_pre tree_edges goods v tp (1 - 1 ) ) ”
  &&  (IntArray.seg ( &( "tmp_" ) ) 0 (1 - 1 ) tp )
  **  (IntArray.undef_seg ( &( "tmp_" ) ) (1 - 1 ) k_pre )
).

Definition solver_entail_wit_9_2 := 
(
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tmpl: (@list Z)) (rows_2: (@list (@list Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (out_2: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (2 <= v)) (PreH19 : (v <= (n_pre + 1 ))) (PreH20 : ((Zlength (out_2)) = (v - 1 ))) (PreH21 : ((Zlength (hd_2)) = n_pre)) (PreH22 : ((Zlength (nx_2)) = (2 * m_pre ))) (PreH23 : ((Zlength (tlst_2)) = (2 * m_pre ))) (PreH24 : ((Zlength (rows_2)) = 105)) (PreH25 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 rows_2 __default__List_Z))) = 100005))) (PreH26 : (BfsRows n_pre tree_edges goods rows_2 (k_pre + 1 ) )) (PreH27 : (OutPrefix n_pre s_pre tree_edges goods out_2 (v - 1 ) )) (PreH28 : ((Zlength (tmpl)) = k_pre)) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out_2 )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd_2 )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx_2 )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst_2 )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full ( &( "tmp_" ) ) k_pre tmpl )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows_2 )
|--
  EX (tp: (@list Z))  (rows: (@list (@list Z)))  (tlst: (@list Z))  (nx: (@list Z))  (hd: (@list Z))  (out: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ ((Zlength (out)) = (v - 1 )) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (k_pre + 1 )) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (rows)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) ) ” 
  &&  “ (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) ) ” 
  &&  “ ((Zlength (tp)) = (1 - 1 )) ” 
  &&  “ (TmpPrefix n_pre tree_edges goods v tp (1 - 1 ) ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.seg ( &( "tmp_" ) ) 0 (1 - 1 ) tp )
  **  (IntArray.undef_seg ( &( "tmp_" ) ) (1 - 1 ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
) \/
(
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tmpl: (@list Z)) (rows_2: (@list (@list Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (out_2: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (2 <= v)) (PreH19 : (v <= (n_pre + 1 ))) (PreH20 : ((Zlength (out_2)) = (v - 1 ))) (PreH21 : ((Zlength (hd_2)) = n_pre)) (PreH22 : ((Zlength (nx_2)) = (2 * m_pre ))) (PreH23 : ((Zlength (tlst_2)) = (2 * m_pre ))) (PreH24 : ((Zlength (rows_2)) = 105)) (PreH25 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 rows_2 __default__List_Z))) = 100005))) (PreH26 : (BfsRows n_pre tree_edges goods rows_2 (k_pre + 1 ) )) (PreH27 : (OutPrefix n_pre s_pre tree_edges goods out_2 (v - 1 ) )) (PreH28 : ((Zlength (tmpl)) = k_pre)) ,
  (IntArray.full ( &( "tmp_" ) ) k_pre tmpl )
|--
  EX (tp: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ ((Zlength (out_2)) = (v - 1 )) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (k_pre + 1 )) ” 
  &&  “ ((Zlength (hd_2)) = n_pre) ” 
  &&  “ ((Zlength (nx_2)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst_2)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (rows_2)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows_2 __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows_2 (k_pre + 1 ) ) ” 
  &&  “ (OutPrefix n_pre s_pre tree_edges goods out_2 (v - 1 ) ) ” 
  &&  “ ((Zlength (tp)) = (1 - 1 )) ” 
  &&  “ (TmpPrefix n_pre tree_edges goods v tp (1 - 1 ) ) ”
  &&  (IntArray.seg ( &( "tmp_" ) ) 0 (1 - 1 ) tp )
  **  (IntArray.undef_seg ( &( "tmp_" ) ) (1 - 1 ) k_pre )
).

Definition solver_entail_wit_10 := 
(
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tp_2: (@list Z)) (rows_2: (@list (@list Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (c: Z) (out_2: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c <= k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out_2)) = (v - 1 ))) (PreH21 : (1 <= c)) (PreH22 : (c <= (k_pre + 1 ))) (PreH23 : ((Zlength (hd_2)) = n_pre)) (PreH24 : ((Zlength (nx_2)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst_2)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows_2)) = 105)) (PreH27 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows_2 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_2 (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out_2 (v - 1 ) )) (PreH30 : ((Zlength (tp_2)) = (c - 1 ))) (PreH31 : (TmpPrefix n_pre tree_edges goods v tp_2 (c - 1 ) )) ,
  (IntArray.seg ( &( "tmp_" ) ) 0 ((c - 1 ) + 1 ) (app (tp_2) ((cons ((Znth (v) ((Znth c rows_2 __default__List_Z)) (0))) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "tmp_" ) ) ((c - 1 ) + 1 ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows_2 )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out_2 )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd_2 )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx_2 )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst_2 )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
|--
  EX (tp: (@list Z))  (rows: (@list (@list Z)))  (tlst: (@list Z))  (nx: (@list Z))  (hd: (@list Z))  (out: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ ((Zlength (out)) = (v - 1 )) ” 
  &&  “ (1 <= (c + 1 )) ” 
  &&  “ ((c + 1 ) <= (k_pre + 1 )) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (rows)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) ) ” 
  &&  “ (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) ) ” 
  &&  “ ((Zlength (tp)) = ((c + 1 ) - 1 )) ” 
  &&  “ (TmpPrefix n_pre tree_edges goods v tp ((c + 1 ) - 1 ) ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.seg ( &( "tmp_" ) ) 0 ((c + 1 ) - 1 ) tp )
  **  (IntArray.undef_seg ( &( "tmp_" ) ) ((c + 1 ) - 1 ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
) \/
(
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tp_2: (@list Z)) (rows_2: (@list (@list Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (c: Z) (out_2: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c <= k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out_2)) = (v - 1 ))) (PreH21 : (1 <= c)) (PreH22 : (c <= (k_pre + 1 ))) (PreH23 : ((Zlength (hd_2)) = n_pre)) (PreH24 : ((Zlength (nx_2)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst_2)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows_2)) = 105)) (PreH27 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows_2 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_2 (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out_2 (v - 1 ) )) (PreH30 : ((Zlength (tp_2)) = (c - 1 ))) (PreH31 : (TmpPrefix n_pre tree_edges goods v tp_2 (c - 1 ) )) ,
  (IntArray.seg ( &( "tmp_" ) ) 0 ((c - 1 ) + 1 ) (app (tp_2) ((cons ((Znth (v) ((Znth c rows_2 __default__List_Z)) (0))) ((@nil Z))))) )
|--
  EX (tp: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ ((Zlength (out_2)) = (v - 1 )) ” 
  &&  “ (1 <= (c + 1 )) ” 
  &&  “ ((c + 1 ) <= (k_pre + 1 )) ” 
  &&  “ ((Zlength (hd_2)) = n_pre) ” 
  &&  “ ((Zlength (nx_2)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst_2)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (rows_2)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows_2 __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows_2 (k_pre + 1 ) ) ” 
  &&  “ (OutPrefix n_pre s_pre tree_edges goods out_2 (v - 1 ) ) ” 
  &&  “ ((Zlength (tp)) = ((c + 1 ) - 1 )) ” 
  &&  “ (TmpPrefix n_pre tree_edges goods v tp ((c + 1 ) - 1 ) ) ”
  &&  (IntArray.seg ( &( "tmp_" ) ) 0 ((c + 1 ) - 1 ) tp )
).

Definition solver_entail_wit_11 := 
(
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tp_2: (@list Z)) (rows_2: (@list (@list Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (c: Z) (out_2: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c > k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out_2)) = (v - 1 ))) (PreH21 : (1 <= c)) (PreH22 : (c <= (k_pre + 1 ))) (PreH23 : ((Zlength (hd_2)) = n_pre)) (PreH24 : ((Zlength (nx_2)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst_2)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows_2)) = 105)) (PreH27 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 rows_2 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_2 (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out_2 (v - 1 ) )) (PreH30 : ((Zlength (tp_2)) = (c - 1 ))) (PreH31 : (TmpPrefix n_pre tree_edges goods v tp_2 (c - 1 ) )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out_2 )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd_2 )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx_2 )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst_2 )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.seg ( &( "tmp_" ) ) 0 (c - 1 ) tp_2 )
  **  (IntArray.undef_seg ( &( "tmp_" ) ) (c - 1 ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows_2 )
|--
  EX (tp: (@list Z))  (rows: (@list (@list Z)))  (tlst: (@list Z))  (nx: (@list Z))  (hd: (@list Z))  (out: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ ((Zlength (out)) = (v - 1 )) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (rows)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) ) ” 
  &&  “ (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) ) ” 
  &&  “ (TmpPrefix n_pre tree_edges goods v tp k_pre ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full (( &( "tmp_" ) ) + (0 * sizeof(INT))) k_pre tp )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
) \/
(
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tp_2: (@list Z)) (rows_2: (@list (@list Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (c: Z) (out_2: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c > k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH12 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out_2)) = (v - 1 ))) (PreH21 : (1 <= c)) (PreH22 : (c <= (k_pre + 1 ))) (PreH23 : ((Zlength (hd_2)) = n_pre)) (PreH24 : ((Zlength (nx_2)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst_2)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows_2)) = 105)) (PreH27 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 rows_2 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_2 (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out_2 (v - 1 ) )) (PreH30 : ((Zlength (tp_2)) = (c - 1 ))) (PreH31 : (TmpPrefix n_pre tree_edges goods v tp_2 (c - 1 ) )) ,
  (IntArray.seg ( &( "tmp_" ) ) 0 (c - 1 ) tp_2 )
|--
  EX (tp: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ ((Zlength (out_2)) = (v - 1 )) ” 
  &&  “ ((Zlength (hd_2)) = n_pre) ” 
  &&  “ ((Zlength (nx_2)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst_2)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (rows_2)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows_2 __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows_2 (k_pre + 1 ) ) ” 
  &&  “ (OutPrefix n_pre s_pre tree_edges goods out_2 (v - 1 ) ) ” 
  &&  “ (TmpPrefix n_pre tree_edges goods v tp k_pre ) ”
  &&  (IntArray.full (( &( "tmp_" ) ) + (0 * sizeof(INT))) k_pre tp )
).

Definition solver_entail_wit_12 := 
(
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd_2: (@list Z)) (nx_2: (@list Z)) (tlst_2: (@list Z)) (rows_2: (@list (@list Z))) (out_2: (@list Z)) (tp: (@list Z)) (v: Z) (l1_2: (@list Z))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (Permutation tp l1_2 )) (PreH2 : (mono_nondec l1_2 )) (PreH3 : (Pre k_pre s_pre tree_edges goods )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (1 <= s_pre)) (PreH9 : (s_pre <= k_pre)) (PreH10 : (k_pre <= 100)) (PreH11 : (k_pre <= n_pre)) (PreH12 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH13 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH14 : (n_pre = (Zlength (goods)))) (PreH15 : (m_pre = (Zlength (tree_edges)))) (PreH16 : ((Zlength (edge_u)) = m_pre)) (PreH17 : ((Zlength (edge_v)) = m_pre)) (PreH18 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH19 : (1 <= v)) (PreH20 : (v <= n_pre)) (PreH21 : ((Zlength (out_2)) = (v - 1 ))) (PreH22 : ((Zlength (hd_2)) = n_pre)) (PreH23 : ((Zlength (nx_2)) = (2 * m_pre ))) (PreH24 : ((Zlength (tlst_2)) = (2 * m_pre ))) (PreH25 : ((Zlength (rows_2)) = 105)) (PreH26 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 rows_2 __default__List_Z))) = 100005))) (PreH27 : (BfsRows n_pre tree_edges goods rows_2 (k_pre + 1 ) )) (PreH28 : (OutPrefix n_pre s_pre tree_edges goods out_2 (v - 1 ) )) (PreH29 : (TmpPrefix n_pre tree_edges goods v tp k_pre )) ,
  (IntArray.full (( &( "tmp_" ) ) + (0 * sizeof(INT))) k_pre l1_2 )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out_2 )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd_2 )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx_2 )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst_2 )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows_2 )
|--
  EX (tp0: (@list Z))  (l1: (@list Z))  (rows: (@list (@list Z)))  (tlst: (@list Z))  (nx: (@list Z))  (hd: (@list Z))  (out: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ ((Zlength (out)) = (v - 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= s_pre) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (rows)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) ) ” 
  &&  “ (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) ) ” 
  &&  “ ((Zlength (l1)) = k_pre) ” 
  &&  “ (mono_nondec l1 ) ” 
  &&  “ ((Zlength (tp0)) = k_pre) ” 
  &&  “ (TmpPrefix n_pre tree_edges goods v tp0 k_pre ) ” 
  &&  “ (Permutation tp0 l1 ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 )))) ” 
  &&  “ (0 = (ZSum ((sublist (0) (0) (l1))))) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full ( &( "tmp_" ) ) k_pre l1 )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
) \/
(
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd_2: (@list Z)) (nx_2: (@list Z)) (tlst_2: (@list Z)) (rows_2: (@list (@list Z))) (out_2: (@list Z)) (tp: (@list Z)) (v: Z) (l1_2: (@list Z))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (Permutation tp l1_2 )) (PreH2 : (mono_nondec l1_2 )) (PreH3 : (Pre k_pre s_pre tree_edges goods )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (1 <= s_pre)) (PreH9 : (s_pre <= k_pre)) (PreH10 : (k_pre <= 100)) (PreH11 : (k_pre <= n_pre)) (PreH12 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))) (PreH13 : forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))) (PreH14 : (n_pre = (Zlength (goods)))) (PreH15 : (m_pre = (Zlength (tree_edges)))) (PreH16 : ((Zlength (edge_u)) = m_pre)) (PreH17 : ((Zlength (edge_v)) = m_pre)) (PreH18 : forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))) (PreH19 : (1 <= v)) (PreH20 : (v <= n_pre)) (PreH21 : ((Zlength (out_2)) = (v - 1 ))) (PreH22 : ((Zlength (hd_2)) = n_pre)) (PreH23 : ((Zlength (nx_2)) = (2 * m_pre ))) (PreH24 : ((Zlength (tlst_2)) = (2 * m_pre ))) (PreH25 : ((Zlength (rows_2)) = 105)) (PreH26 : forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 rows_2 __default__List_Z))) = 100005))) (PreH27 : (BfsRows n_pre tree_edges goods rows_2 (k_pre + 1 ) )) (PreH28 : (OutPrefix n_pre s_pre tree_edges goods out_2 (v - 1 ) )) (PreH29 : (TmpPrefix n_pre tree_edges goods v tp k_pre )) ,
  (IntArray.full (( &( "tmp_" ) ) + (0 * sizeof(INT))) k_pre l1_2 )
|--
  EX (tp0: (@list Z))  (l1: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ ((Zlength (out_2)) = (v - 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= s_pre) ” 
  &&  “ ((Zlength (hd_2)) = n_pre) ” 
  &&  “ ((Zlength (nx_2)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst_2)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (rows_2)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows_2 __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows_2 (k_pre + 1 ) ) ” 
  &&  “ (OutPrefix n_pre s_pre tree_edges goods out_2 (v - 1 ) ) ” 
  &&  “ ((Zlength (l1)) = k_pre) ” 
  &&  “ (mono_nondec l1 ) ” 
  &&  “ ((Zlength (tp0)) = k_pre) ” 
  &&  “ (TmpPrefix n_pre tree_edges goods v tp0 k_pre ) ” 
  &&  “ (Permutation tp0 l1 ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 )))) ” 
  &&  “ (0 = (ZSum ((sublist (0) (0) (l1))))) ”
  &&  (IntArray.full ( &( "tmp_" ) ) k_pre l1 )
).

Definition solver_entail_wit_13 := 
(
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (sum: Z) (tp0_2: (@list Z)) (l1_2: (@list Z)) (rows_2: (@list (@list Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (i_4: Z) (out_2: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < s_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out_2)) = (v - 1 ))) (PreH21 : (0 <= i_4)) (PreH22 : (i_4 <= s_pre)) (PreH23 : ((Zlength (hd_2)) = n_pre)) (PreH24 : ((Zlength (nx_2)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst_2)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows_2)) = 105)) (PreH27 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows_2 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_2 (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out_2 (v - 1 ) )) (PreH30 : ((Zlength (l1_2)) = k_pre)) (PreH31 : (mono_nondec l1_2 )) (PreH32 : ((Zlength (tp0_2)) = k_pre)) (PreH33 : (TmpPrefix n_pre tree_edges goods v tp0_2 k_pre )) (PreH34 : (Permutation tp0_2 l1_2 )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1_2 0)) /\ ((Znth j l1_2 0) <= (n_pre - 1 ))))) (PreH36 : (sum = (ZSum ((sublist (0) (i_4) (l1_2)))))) ,
  (IntArray.full ( &( "tmp_" ) ) k_pre l1_2 )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out_2 )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd_2 )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx_2 )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst_2 )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows_2 )
|--
  EX (tp0: (@list Z))  (l1: (@list Z))  (rows: (@list (@list Z)))  (tlst: (@list Z))  (nx: (@list Z))  (hd: (@list Z))  (out: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ ((Zlength (out)) = (v - 1 )) ” 
  &&  “ (0 <= (i_4 + 1 )) ” 
  &&  “ ((i_4 + 1 ) <= s_pre) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (rows)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) ) ” 
  &&  “ (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) ) ” 
  &&  “ ((Zlength (l1)) = k_pre) ” 
  &&  “ (mono_nondec l1 ) ” 
  &&  “ ((Zlength (tp0)) = k_pre) ” 
  &&  “ (TmpPrefix n_pre tree_edges goods v tp0 k_pre ) ” 
  &&  “ (Permutation tp0 l1 ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 )))) ” 
  &&  “ ((sum + (Znth i_4 l1_2 0) ) = (ZSum ((sublist (0) ((i_4 + 1 )) (l1))))) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full ( &( "tmp_" ) ) k_pre l1 )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
) \/
(
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (sum: Z) (tp0_2: (@list Z)) (l1_2: (@list Z)) (rows_2: (@list (@list Z))) (tlst_2: (@list Z)) (nx_2: (@list Z)) (hd_2: (@list Z)) (i_4: Z) (out_2: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < s_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out_2)) = (v - 1 ))) (PreH21 : (0 <= i_4)) (PreH22 : (i_4 <= s_pre)) (PreH23 : ((Zlength (hd_2)) = n_pre)) (PreH24 : ((Zlength (nx_2)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst_2)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows_2)) = 105)) (PreH27 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows_2 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_2 (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out_2 (v - 1 ) )) (PreH30 : ((Zlength (l1_2)) = k_pre)) (PreH31 : (mono_nondec l1_2 )) (PreH32 : ((Zlength (tp0_2)) = k_pre)) (PreH33 : (TmpPrefix n_pre tree_edges goods v tp0_2 k_pre )) (PreH34 : (Permutation tp0_2 l1_2 )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1_2 0)) /\ ((Znth j l1_2 0) <= (n_pre - 1 ))))) (PreH36 : (sum = (ZSum ((sublist (0) (i_4) (l1_2)))))) ,
  TT && emp 
|--
  EX (tp0: (@list Z)) ,
  “ (0 <= (i_4 + 1 )) ” 
  &&  “ ((i_4 + 1 ) <= s_pre) ” 
  &&  “ ((Zlength (tp0)) = (Zlength (l1_2))) ” 
  &&  “ (TmpPrefix (Zlength (goods)) tree_edges goods v tp0 (Zlength (l1_2)) ) ” 
  &&  “ (Permutation tp0 l1_2 ) ” 
  &&  “ (((ZSum ((sublist (0) (i_4) (l1_2)))) + (Znth i_4 l1_2 0) ) = (ZSum ((sublist (0) ((i_4 + 1 )) (l1_2))))) ”
  &&  emp
).

Definition solver_entail_wit_14 := 
(
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (sum: Z) (tp0: (@list Z)) (l1: (@list Z)) (rows_3: (@list (@list Z))) (tlst_3: (@list Z)) (nx_3: (@list Z)) (hd_3: (@list Z)) (i_10: Z) (out_3: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_10 >= s_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_7: Z) , (((0 <= i_7) /\ (i_7 < n_pre)) -> ((1 <= (Znth i_7 goods 0)) /\ ((Znth i_7 goods 0) <= k_pre)))) (PreH12 : forall (i_8: Z) , (((0 <= i_8) /\ (i_8 < m_pre)) -> (((((1 <= (fst ((Znth i_8 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_9: Z) , (((0 <= i_9) /\ (i_9 < m_pre)) -> (((Znth i_9 edge_u 0) = (fst ((Znth i_9 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_9 edge_v 0) = (snd ((Znth i_9 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out_3)) = (v - 1 ))) (PreH21 : (0 <= i_10)) (PreH22 : (i_10 <= s_pre)) (PreH23 : ((Zlength (hd_3)) = n_pre)) (PreH24 : ((Zlength (nx_3)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst_3)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows_3)) = 105)) (PreH27 : forall (cc_3: Z) , (((0 <= cc_3) /\ (cc_3 < 105)) -> ((Zlength ((Znth cc_3 rows_3 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_3 (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out_3 (v - 1 ) )) (PreH30 : ((Zlength (l1)) = k_pre)) (PreH31 : (mono_nondec l1 )) (PreH32 : ((Zlength (tp0)) = k_pre)) (PreH33 : (TmpPrefix n_pre tree_edges goods v tp0 k_pre )) (PreH34 : (Permutation tp0 l1 )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 ))))) (PreH36 : (sum = (ZSum ((sublist (0) (i_10) (l1)))))) ,
  (Int64Array.seg cost_pre 1 (v + 1 ) (app (out_3) ((cons (sum) ((@nil Z))))) )
  **  (Int64Array.undef_seg cost_pre (v + 1 ) (n_pre + 1 ) )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd_3 )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx_3 )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst_3 )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full ( &( "tmp_" ) ) k_pre l1 )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows_3 )
|--
  EX (tmpl: (@list Z))  (rows_2: (@list (@list Z)))  (tlst_2: (@list Z))  (nx_2: (@list Z))  (hd_2: (@list Z))  (out_2: (@list Z)) ,
  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre))) ” 
  &&  “ forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (2 <= (v + 1 )) ” 
  &&  “ ((v + 1 ) <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (out_2)) = ((v + 1 ) - 1 )) ” 
  &&  “ ((Zlength (hd_2)) = n_pre) ” 
  &&  “ ((Zlength (nx_2)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst_2)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (rows_2)) = 105) ” 
  &&  “ forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 rows_2 __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows_2 (k_pre + 1 ) ) ” 
  &&  “ (OutPrefix n_pre s_pre tree_edges goods out_2 ((v + 1 ) - 1 ) ) ” 
  &&  “ ((Zlength (tmpl)) = k_pre) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 (v + 1 ) out_2 )
  **  (Int64Array.undef_seg cost_pre (v + 1 ) (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd_2 )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx_2 )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst_2 )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full ( &( "tmp_" ) ) k_pre tmpl )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows_2 )
) \/
(
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (sum: Z) (tp0: (@list Z)) (l1: (@list Z)) (rows_3: (@list (@list Z))) (tlst_3: (@list Z)) (nx_3: (@list Z)) (hd_3: (@list Z)) (i_10: Z) (out_3: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_10 >= s_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_7: Z) , (((0 <= i_7) /\ (i_7 < n_pre)) -> ((1 <= (Znth i_7 goods 0)) /\ ((Znth i_7 goods 0) <= k_pre)))) (PreH12 : forall (i_8: Z) , (((0 <= i_8) /\ (i_8 < m_pre)) -> (((((1 <= (fst ((Znth i_8 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_9: Z) , (((0 <= i_9) /\ (i_9 < m_pre)) -> (((Znth i_9 edge_u 0) = (fst ((Znth i_9 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_9 edge_v 0) = (snd ((Znth i_9 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out_3)) = (v - 1 ))) (PreH21 : (0 <= i_10)) (PreH22 : (i_10 <= s_pre)) (PreH23 : ((Zlength (hd_3)) = n_pre)) (PreH24 : ((Zlength (nx_3)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst_3)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows_3)) = 105)) (PreH27 : forall (cc_3: Z) , (((0 <= cc_3) /\ (cc_3 < 105)) -> ((Zlength ((Znth cc_3 rows_3 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_3 (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out_3 (v - 1 ) )) (PreH30 : ((Zlength (l1)) = k_pre)) (PreH31 : (mono_nondec l1 )) (PreH32 : ((Zlength (tp0)) = k_pre)) (PreH33 : (TmpPrefix n_pre tree_edges goods v tp0 k_pre )) (PreH34 : (Permutation tp0 l1 )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 ))))) (PreH36 : (sum = (ZSum ((sublist (0) (i_10) (l1)))))) ,
  TT && emp 
|--
  “ (OutPrefix n_pre s_pre tree_edges goods (app (out_3) ((cons (sum) ((@nil Z))))) ((v + 1 ) - 1 ) ) ” 
  &&  “ forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 rows_3 __default__List_Z))) = 100005)) ” 
  &&  “ ((Zlength ((app (out_3) ((cons (sum) ((@nil Z))))))) = ((v + 1 ) - 1 )) ” 
  &&  “ forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre))) ”
  &&  emp
).

Definition solver_entail_wit_14_split_goal_1 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (sum: Z) (tp0: (@list Z)) (l1: (@list Z)) (rows_3: (@list (@list Z))) (tlst_3: (@list Z)) (nx_3: (@list Z)) (hd_3: (@list Z)) (i_10: Z) (out_3: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_10 >= s_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_7: Z) , (((0 <= i_7) /\ (i_7 < n_pre)) -> ((1 <= (Znth i_7 goods 0)) /\ ((Znth i_7 goods 0) <= k_pre)))) (PreH12 : forall (i_8: Z) , (((0 <= i_8) /\ (i_8 < m_pre)) -> (((((1 <= (fst ((Znth i_8 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_9: Z) , (((0 <= i_9) /\ (i_9 < m_pre)) -> (((Znth i_9 edge_u 0) = (fst ((Znth i_9 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_9 edge_v 0) = (snd ((Znth i_9 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out_3)) = (v - 1 ))) (PreH21 : (0 <= i_10)) (PreH22 : (i_10 <= s_pre)) (PreH23 : ((Zlength (hd_3)) = n_pre)) (PreH24 : ((Zlength (nx_3)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst_3)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows_3)) = 105)) (PreH27 : forall (cc_3: Z) , (((0 <= cc_3) /\ (cc_3 < 105)) -> ((Zlength ((Znth cc_3 rows_3 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_3 (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out_3 (v - 1 ) )) (PreH30 : ((Zlength (l1)) = k_pre)) (PreH31 : (mono_nondec l1 )) (PreH32 : ((Zlength (tp0)) = k_pre)) (PreH33 : (TmpPrefix n_pre tree_edges goods v tp0 k_pre )) (PreH34 : (Permutation tp0 l1 )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 ))))) (PreH36 : (sum = (ZSum ((sublist (0) (i_10) (l1)))))) ,
  (OutPrefix n_pre s_pre tree_edges goods (app (out_3) ((cons (sum) ((@nil Z))))) ((v + 1 ) - 1 ) )
.

Definition solver_entail_wit_14_split_goal_2 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (sum: Z) (tp0: (@list Z)) (l1: (@list Z)) (rows_3: (@list (@list Z))) (tlst_3: (@list Z)) (nx_3: (@list Z)) (hd_3: (@list Z)) (i_10: Z) (out_3: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_10 >= s_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_7: Z) , (((0 <= i_7) /\ (i_7 < n_pre)) -> ((1 <= (Znth i_7 goods 0)) /\ ((Znth i_7 goods 0) <= k_pre)))) (PreH12 : forall (i_8: Z) , (((0 <= i_8) /\ (i_8 < m_pre)) -> (((((1 <= (fst ((Znth i_8 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_9: Z) , (((0 <= i_9) /\ (i_9 < m_pre)) -> (((Znth i_9 edge_u 0) = (fst ((Znth i_9 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_9 edge_v 0) = (snd ((Znth i_9 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out_3)) = (v - 1 ))) (PreH21 : (0 <= i_10)) (PreH22 : (i_10 <= s_pre)) (PreH23 : ((Zlength (hd_3)) = n_pre)) (PreH24 : ((Zlength (nx_3)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst_3)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows_3)) = 105)) (PreH27 : forall (cc_3: Z) , (((0 <= cc_3) /\ (cc_3 < 105)) -> ((Zlength ((Znth cc_3 rows_3 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_3 (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out_3 (v - 1 ) )) (PreH30 : ((Zlength (l1)) = k_pre)) (PreH31 : (mono_nondec l1 )) (PreH32 : ((Zlength (tp0)) = k_pre)) (PreH33 : (TmpPrefix n_pre tree_edges goods v tp0 k_pre )) (PreH34 : (Permutation tp0 l1 )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 ))))) (PreH36 : (sum = (ZSum ((sublist (0) (i_10) (l1)))))) ,
  forall (cc_2: Z) , (((0 <= cc_2) /\ (cc_2 < 105)) -> ((Zlength ((Znth cc_2 rows_3 __default__List_Z))) = 100005))
.

Definition solver_entail_wit_14_split_goal_3 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (sum: Z) (tp0: (@list Z)) (l1: (@list Z)) (rows_3: (@list (@list Z))) (tlst_3: (@list Z)) (nx_3: (@list Z)) (hd_3: (@list Z)) (i_10: Z) (out_3: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_10 >= s_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_7: Z) , (((0 <= i_7) /\ (i_7 < n_pre)) -> ((1 <= (Znth i_7 goods 0)) /\ ((Znth i_7 goods 0) <= k_pre)))) (PreH12 : forall (i_8: Z) , (((0 <= i_8) /\ (i_8 < m_pre)) -> (((((1 <= (fst ((Znth i_8 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_9: Z) , (((0 <= i_9) /\ (i_9 < m_pre)) -> (((Znth i_9 edge_u 0) = (fst ((Znth i_9 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_9 edge_v 0) = (snd ((Znth i_9 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out_3)) = (v - 1 ))) (PreH21 : (0 <= i_10)) (PreH22 : (i_10 <= s_pre)) (PreH23 : ((Zlength (hd_3)) = n_pre)) (PreH24 : ((Zlength (nx_3)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst_3)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows_3)) = 105)) (PreH27 : forall (cc_3: Z) , (((0 <= cc_3) /\ (cc_3 < 105)) -> ((Zlength ((Znth cc_3 rows_3 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_3 (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out_3 (v - 1 ) )) (PreH30 : ((Zlength (l1)) = k_pre)) (PreH31 : (mono_nondec l1 )) (PreH32 : ((Zlength (tp0)) = k_pre)) (PreH33 : (TmpPrefix n_pre tree_edges goods v tp0 k_pre )) (PreH34 : (Permutation tp0 l1 )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 ))))) (PreH36 : (sum = (ZSum ((sublist (0) (i_10) (l1)))))) ,
  ((Zlength ((app (out_3) ((cons (sum) ((@nil Z))))))) = ((v + 1 ) - 1 ))
.

Definition solver_entail_wit_14_split_goal_4 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (sum: Z) (tp0: (@list Z)) (l1: (@list Z)) (rows_3: (@list (@list Z))) (tlst_3: (@list Z)) (nx_3: (@list Z)) (hd_3: (@list Z)) (i_10: Z) (out_3: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_10 >= s_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_7: Z) , (((0 <= i_7) /\ (i_7 < n_pre)) -> ((1 <= (Znth i_7 goods 0)) /\ ((Znth i_7 goods 0) <= k_pre)))) (PreH12 : forall (i_8: Z) , (((0 <= i_8) /\ (i_8 < m_pre)) -> (((((1 <= (fst ((Znth i_8 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_9: Z) , (((0 <= i_9) /\ (i_9 < m_pre)) -> (((Znth i_9 edge_u 0) = (fst ((Znth i_9 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_9 edge_v 0) = (snd ((Znth i_9 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out_3)) = (v - 1 ))) (PreH21 : (0 <= i_10)) (PreH22 : (i_10 <= s_pre)) (PreH23 : ((Zlength (hd_3)) = n_pre)) (PreH24 : ((Zlength (nx_3)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst_3)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows_3)) = 105)) (PreH27 : forall (cc_3: Z) , (((0 <= cc_3) /\ (cc_3 < 105)) -> ((Zlength ((Znth cc_3 rows_3 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_3 (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out_3 (v - 1 ) )) (PreH30 : ((Zlength (l1)) = k_pre)) (PreH31 : (mono_nondec l1 )) (PreH32 : ((Zlength (tp0)) = k_pre)) (PreH33 : (TmpPrefix n_pre tree_edges goods v tp0 k_pre )) (PreH34 : (Permutation tp0 l1 )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 ))))) (PreH36 : (sum = (ZSum ((sublist (0) (i_10) (l1)))))) ,
  forall (i_6: Z) , (((0 <= i_6) /\ (i_6 < m_pre)) -> (((Znth i_6 edge_u 0) = (fst ((Znth i_6 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_6 edge_v 0) = (snd ((Znth i_6 tree_edges __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_14_split_goal_5 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (sum: Z) (tp0: (@list Z)) (l1: (@list Z)) (rows_3: (@list (@list Z))) (tlst_3: (@list Z)) (nx_3: (@list Z)) (hd_3: (@list Z)) (i_10: Z) (out_3: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_10 >= s_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_7: Z) , (((0 <= i_7) /\ (i_7 < n_pre)) -> ((1 <= (Znth i_7 goods 0)) /\ ((Znth i_7 goods 0) <= k_pre)))) (PreH12 : forall (i_8: Z) , (((0 <= i_8) /\ (i_8 < m_pre)) -> (((((1 <= (fst ((Znth i_8 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_9: Z) , (((0 <= i_9) /\ (i_9 < m_pre)) -> (((Znth i_9 edge_u 0) = (fst ((Znth i_9 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_9 edge_v 0) = (snd ((Znth i_9 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out_3)) = (v - 1 ))) (PreH21 : (0 <= i_10)) (PreH22 : (i_10 <= s_pre)) (PreH23 : ((Zlength (hd_3)) = n_pre)) (PreH24 : ((Zlength (nx_3)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst_3)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows_3)) = 105)) (PreH27 : forall (cc_3: Z) , (((0 <= cc_3) /\ (cc_3 < 105)) -> ((Zlength ((Znth cc_3 rows_3 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_3 (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out_3 (v - 1 ) )) (PreH30 : ((Zlength (l1)) = k_pre)) (PreH31 : (mono_nondec l1 )) (PreH32 : ((Zlength (tp0)) = k_pre)) (PreH33 : (TmpPrefix n_pre tree_edges goods v tp0 k_pre )) (PreH34 : (Permutation tp0 l1 )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 ))))) (PreH36 : (sum = (ZSum ((sublist (0) (i_10) (l1)))))) ,
  forall (i_5: Z) , (((0 <= i_5) /\ (i_5 < m_pre)) -> (((((1 <= (fst ((Znth i_5 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_5 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_5 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_5 tree_edges __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_14_split_goal_6 := 
forall (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (sum: Z) (tp0: (@list Z)) (l1: (@list Z)) (rows_3: (@list (@list Z))) (tlst_3: (@list Z)) (nx_3: (@list Z)) (hd_3: (@list Z)) (i_10: Z) (out_3: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_10 >= s_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i_7: Z) , (((0 <= i_7) /\ (i_7 < n_pre)) -> ((1 <= (Znth i_7 goods 0)) /\ ((Znth i_7 goods 0) <= k_pre)))) (PreH12 : forall (i_8: Z) , (((0 <= i_8) /\ (i_8 < m_pre)) -> (((((1 <= (fst ((Znth i_8 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_8 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_8 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_8 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_9: Z) , (((0 <= i_9) /\ (i_9 < m_pre)) -> (((Znth i_9 edge_u 0) = (fst ((Znth i_9 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_9 edge_v 0) = (snd ((Znth i_9 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out_3)) = (v - 1 ))) (PreH21 : (0 <= i_10)) (PreH22 : (i_10 <= s_pre)) (PreH23 : ((Zlength (hd_3)) = n_pre)) (PreH24 : ((Zlength (nx_3)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst_3)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows_3)) = 105)) (PreH27 : forall (cc_3: Z) , (((0 <= cc_3) /\ (cc_3 < 105)) -> ((Zlength ((Znth cc_3 rows_3 __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows_3 (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out_3 (v - 1 ) )) (PreH30 : ((Zlength (l1)) = k_pre)) (PreH31 : (mono_nondec l1 )) (PreH32 : ((Zlength (tp0)) = k_pre)) (PreH33 : (TmpPrefix n_pre tree_edges goods v tp0 k_pre )) (PreH34 : (Permutation tp0 l1 )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 ))))) (PreH36 : (sum = (ZSum ((sublist (0) (i_10) (l1)))))) ,
  forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < n_pre)) -> ((1 <= (Znth i_4 goods 0)) /\ ((Znth i_4 goods 0) <= k_pre)))
.

Definition solver_return_wit_1 := 
(
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tmpl: (@list Z)) (rows: (@list (@list Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (out_2: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (v > n_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (2 <= v)) (PreH19 : (v <= (n_pre + 1 ))) (PreH20 : ((Zlength (out_2)) = (v - 1 ))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * m_pre ))) (PreH23 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH24 : ((Zlength (rows)) = 105)) (PreH25 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH26 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH27 : (OutPrefix n_pre s_pre tree_edges goods out_2 (v - 1 ) )) (PreH28 : ((Zlength (tmpl)) = k_pre)) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out_2 )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full ( &( "tmp_" ) ) k_pre tmpl )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  EX (tmp_after: (@list Z))  (to_after: (@list Z))  (nxt_after: (@list Z))  (head_after: (@list Z))  (dist_after: (@list (@list Z)))  (out: (@list Z)) ,
  “ (Spec k_pre s_pre tree_edges goods out ) ” 
  &&  “ ((Zlength (out)) = n_pre) ” 
  &&  “ ((Zlength (dist_after)) = 105) ” 
  &&  “ forall (c: Z) , (((0 <= c) /\ (c < 105)) -> ((Zlength ((Znth c dist_after __default__List_Z))) = 100005)) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 (n_pre + 1 ) out )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) head_after )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nxt_after )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) to_after )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full ( &( "tmp_" ) ) k_pre tmp_after )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_after )
) \/
(
forall (cost_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tmpl: (@list Z)) (rows: (@list (@list Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (out_2: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (v > n_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (2 <= v)) (PreH19 : (v <= (n_pre + 1 ))) (PreH20 : ((Zlength (out_2)) = (v - 1 ))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * m_pre ))) (PreH23 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH24 : ((Zlength (rows)) = 105)) (PreH25 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH26 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH27 : (OutPrefix n_pre s_pre tree_edges goods out_2 (v - 1 ) )) (PreH28 : ((Zlength (tmpl)) = k_pre)) ,
  (Int64Array.seg cost_pre 1 v out_2 )
|--
  EX (out: (@list Z)) ,
  “ (Spec k_pre s_pre tree_edges goods out ) ” 
  &&  “ ((Zlength (out)) = n_pre) ” 
  &&  “ ((Zlength (rows)) = 105) ” 
  &&  “ forall (c: Z) , (((0 <= c) /\ (c < 105)) -> ((Zlength ((Znth c rows __default__List_Z))) = 100005)) ”
  &&  (Int64Array.seg cost_pre 1 (n_pre + 1 ) out )
).

Definition solver_partial_solve_wit_1 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd0: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (v <= n_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= (n_pre + 1 ))) (PreH20 : ((Zlength (hd0)) = (v - 1 ))) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < (v - 1 ))) -> ((Znth j hd0 0) = (-1)))) (PreH22 : ((Zlength (dist_before)) = 105)) (PreH23 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 v hd0 )
  **  (IntArray.undef_seg ( &( "head_" ) ) v (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "nxt_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "to_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (v <= n_pre) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (hd0)) = (v - 1 )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (v - 1 ))) -> ((Znth j hd0 0) = (-1))) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (((( &( "head_" ) ) + (v * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "head_" ) ) (v + 1 ) (n_pre + 1 ) )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 v hd0 )
  **  (IntArray.undef_full ( &( "nxt_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "to_" ) ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
.

Definition solver_partial_solve_wit_2 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd nx tlst )) (PreH25 : (NxtRange i_4 nx )) (PreH26 : (ArcToRange n_pre i_4 tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (2 * i_4 ) nx )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (2 * i_4 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 (2 * i_4 ) tlst )
  **  (IntArray.undef_seg ( &( "to_" ) ) (2 * i_4 ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (i_4 < m_pre) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i_4) ” 
  &&  “ (i_4 <= m_pre) ” 
  &&  “ ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre))) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * i_4 )) ” 
  &&  “ ((Zlength (tlst)) = (2 * i_4 )) ” 
  &&  “ (AdjBuild n_pre i_4 tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange i_4 nx ) ” 
  &&  “ (ArcToRange n_pre i_4 tlst ) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (((ev_pre + (i_4 * sizeof(INT)))) # Int  |-> (Znth i_4 edge_v 0))
  **  (IntArray.missing_i ev_pre i_4 0 m_pre edge_v )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (2 * i_4 ) nx )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (2 * i_4 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 (2 * i_4 ) tlst )
  **  (IntArray.undef_seg ( &( "to_" ) ) (2 * i_4 ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
.

Definition solver_partial_solve_wit_3 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd nx tlst )) (PreH25 : (NxtRange i_4 nx )) (PreH26 : (ArcToRange n_pre i_4 tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (2 * i_4 ) nx )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (2 * i_4 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 (2 * i_4 ) tlst )
  **  (IntArray.undef_seg ( &( "to_" ) ) (2 * i_4 ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (i_4 < m_pre) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i_4) ” 
  &&  “ (i_4 <= m_pre) ” 
  &&  “ ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre))) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * i_4 )) ” 
  &&  “ ((Zlength (tlst)) = (2 * i_4 )) ” 
  &&  “ (AdjBuild n_pre i_4 tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange i_4 nx ) ” 
  &&  “ (ArcToRange n_pre i_4 tlst ) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (((( &( "to_" ) ) + ((2 * i_4 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "to_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (2 * i_4 ) nx )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (2 * i_4 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 (2 * i_4 ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
.

Definition solver_partial_solve_wit_4 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd nx tlst )) (PreH25 : (NxtRange i_4 nx )) (PreH26 : (ArcToRange n_pre i_4 tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg ( &( "to_" ) ) 0 ((2 * i_4 ) + 1 ) (app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (2 * i_4 ) nx )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (2 * i_4 ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (i_4 < m_pre) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i_4) ” 
  &&  “ (i_4 <= m_pre) ” 
  &&  “ ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre))) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * i_4 )) ” 
  &&  “ ((Zlength (tlst)) = (2 * i_4 )) ” 
  &&  “ (AdjBuild n_pre i_4 tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange i_4 nx ) ” 
  &&  “ (ArcToRange n_pre i_4 tlst ) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (((eu_pre + (i_4 * sizeof(INT)))) # Int  |-> (Znth i_4 edge_u 0))
  **  (IntArray.missing_i eu_pre i_4 0 m_pre edge_u )
  **  (IntArray.seg ( &( "to_" ) ) 0 ((2 * i_4 ) + 1 ) (app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (2 * i_4 ) nx )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (2 * i_4 ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
.

Definition solver_partial_solve_wit_5 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd nx tlst )) (PreH25 : (NxtRange i_4 nx )) (PreH26 : (ArcToRange n_pre i_4 tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg ( &( "to_" ) ) 0 ((2 * i_4 ) + 1 ) (app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (2 * i_4 ) nx )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (2 * i_4 ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (i_4 < m_pre) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i_4) ” 
  &&  “ (i_4 <= m_pre) ” 
  &&  “ ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre))) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * i_4 )) ” 
  &&  “ ((Zlength (tlst)) = (2 * i_4 )) ” 
  &&  “ (AdjBuild n_pre i_4 tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange i_4 nx ) ” 
  &&  “ (ArcToRange n_pre i_4 tlst ) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (((( &( "head_" ) ) + ((Znth i_4 edge_u 0) * sizeof(INT)))) # Int  |-> (Znth ((Znth i_4 edge_u 0) - 1 ) hd 0))
  **  (IntArray.missing_i ( &( "head_" ) ) (Znth i_4 edge_u 0) 1 (n_pre + 1 ) hd )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg ( &( "to_" ) ) 0 ((2 * i_4 ) + 1 ) (app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (2 * i_4 ) nx )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (2 * i_4 ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
.

Definition solver_partial_solve_wit_6 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd nx tlst )) (PreH25 : (NxtRange i_4 nx )) (PreH26 : (ArcToRange n_pre i_4 tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg ( &( "to_" ) ) 0 ((2 * i_4 ) + 1 ) (app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (2 * i_4 ) nx )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (2 * i_4 ) (2 * m_pre ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (i_4 < m_pre) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i_4) ” 
  &&  “ (i_4 <= m_pre) ” 
  &&  “ ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre))) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * i_4 )) ” 
  &&  “ ((Zlength (tlst)) = (2 * i_4 )) ” 
  &&  “ (AdjBuild n_pre i_4 tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange i_4 nx ) ” 
  &&  “ (ArcToRange n_pre i_4 tlst ) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (((( &( "nxt_" ) ) + ((2 * i_4 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "nxt_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg ( &( "to_" ) ) 0 ((2 * i_4 ) + 1 ) (app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (2 * i_4 ) nx )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
.

Definition solver_partial_solve_wit_7 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd nx tlst )) (PreH25 : (NxtRange i_4 nx )) (PreH26 : (ArcToRange n_pre i_4 tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg ( &( "nxt_" ) ) 0 ((2 * i_4 ) + 1 ) (app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg ( &( "to_" ) ) 0 ((2 * i_4 ) + 1 ) (app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (i_4 < m_pre) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i_4) ” 
  &&  “ (i_4 <= m_pre) ” 
  &&  “ ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre))) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * i_4 )) ” 
  &&  “ ((Zlength (tlst)) = (2 * i_4 )) ” 
  &&  “ (AdjBuild n_pre i_4 tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange i_4 nx ) ” 
  &&  “ (ArcToRange n_pre i_4 tlst ) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (((eu_pre + (i_4 * sizeof(INT)))) # Int  |-> (Znth i_4 edge_u 0))
  **  (IntArray.missing_i eu_pre i_4 0 m_pre edge_u )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 ((2 * i_4 ) + 1 ) (app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.seg ( &( "to_" ) ) 0 ((2 * i_4 ) + 1 ) (app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
.

Definition solver_partial_solve_wit_8 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd nx tlst )) (PreH25 : (NxtRange i_4 nx )) (PreH26 : (ArcToRange n_pre i_4 tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 ((2 * i_4 ) + 1 ) (app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.seg ( &( "to_" ) ) 0 ((2 * i_4 ) + 1 ) (app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (i_4 < m_pre) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i_4) ” 
  &&  “ (i_4 <= m_pre) ” 
  &&  “ ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre))) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * i_4 )) ” 
  &&  “ ((Zlength (tlst)) = (2 * i_4 )) ” 
  &&  “ (AdjBuild n_pre i_4 tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange i_4 nx ) ” 
  &&  “ (ArcToRange n_pre i_4 tlst ) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (((( &( "head_" ) ) + ((Znth i_4 edge_u 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "head_" ) ) (Znth i_4 edge_u 0) 1 (n_pre + 1 ) hd )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 ((2 * i_4 ) + 1 ) (app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 ((2 * i_4 ) + 1 ) (app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
.

Definition solver_partial_solve_wit_9 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd nx tlst )) (PreH25 : (NxtRange i_4 nx )) (PreH26 : (ArcToRange n_pre i_4 tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 ((2 * i_4 ) + 1 ) (app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 ((2 * i_4 ) + 1 ) (app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (i_4 < m_pre) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i_4) ” 
  &&  “ (i_4 <= m_pre) ” 
  &&  “ ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre))) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * i_4 )) ” 
  &&  “ ((Zlength (tlst)) = (2 * i_4 )) ” 
  &&  “ (AdjBuild n_pre i_4 tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange i_4 nx ) ” 
  &&  “ (ArcToRange n_pre i_4 tlst ) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (((eu_pre + (i_4 * sizeof(INT)))) # Int  |-> (Znth i_4 edge_u 0))
  **  (IntArray.missing_i eu_pre i_4 0 m_pre edge_u )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 ((2 * i_4 ) + 1 ) (app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 ((2 * i_4 ) + 1 ) (app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
.

Definition solver_partial_solve_wit_10 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd nx tlst )) (PreH25 : (NxtRange i_4 nx )) (PreH26 : (ArcToRange n_pre i_4 tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 ((2 * i_4 ) + 1 ) (app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 ((2 * i_4 ) + 1 ) (app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (i_4 < m_pre) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i_4) ” 
  &&  “ (i_4 <= m_pre) ” 
  &&  “ ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre))) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * i_4 )) ” 
  &&  “ ((Zlength (tlst)) = (2 * i_4 )) ” 
  &&  “ (AdjBuild n_pre i_4 tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange i_4 nx ) ” 
  &&  “ (ArcToRange n_pre i_4 tlst ) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (((( &( "to_" ) ) + (((2 * i_4 ) + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "to_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 ((2 * i_4 ) + 1 ) (app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 ((2 * i_4 ) + 1 ) (app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z))))) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
.

Definition solver_partial_solve_wit_11 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd nx tlst )) (PreH25 : (NxtRange i_4 nx )) (PreH26 : (ArcToRange n_pre i_4 tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg ( &( "to_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z)))))) ((cons ((Znth i_4 edge_u 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 ((2 * i_4 ) + 1 ) (app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (i_4 < m_pre) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i_4) ” 
  &&  “ (i_4 <= m_pre) ” 
  &&  “ ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre))) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * i_4 )) ” 
  &&  “ ((Zlength (tlst)) = (2 * i_4 )) ” 
  &&  “ (AdjBuild n_pre i_4 tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange i_4 nx ) ” 
  &&  “ (ArcToRange n_pre i_4 tlst ) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (((ev_pre + (i_4 * sizeof(INT)))) # Int  |-> (Znth i_4 edge_v 0))
  **  (IntArray.missing_i ev_pre i_4 0 m_pre edge_v )
  **  (IntArray.seg ( &( "to_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z)))))) ((cons ((Znth i_4 edge_u 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 ((2 * i_4 ) + 1 ) (app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
.

Definition solver_partial_solve_wit_12 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd nx tlst )) (PreH25 : (NxtRange i_4 nx )) (PreH26 : (ArcToRange n_pre i_4 tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg ( &( "to_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z)))))) ((cons ((Znth i_4 edge_u 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 ((2 * i_4 ) + 1 ) (app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (i_4 < m_pre) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i_4) ” 
  &&  “ (i_4 <= m_pre) ” 
  &&  “ ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre))) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * i_4 )) ” 
  &&  “ ((Zlength (tlst)) = (2 * i_4 )) ” 
  &&  “ (AdjBuild n_pre i_4 tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange i_4 nx ) ” 
  &&  “ (ArcToRange n_pre i_4 tlst ) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (((( &( "head_" ) ) + ((Znth i_4 edge_v 0) * sizeof(INT)))) # Int  |-> (Znth ((Znth i_4 edge_v 0) - 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) 0))
  **  (IntArray.missing_i ( &( "head_" ) ) (Znth i_4 edge_v 0) 1 (n_pre + 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg ( &( "to_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z)))))) ((cons ((Znth i_4 edge_u 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 ((2 * i_4 ) + 1 ) (app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
.

Definition solver_partial_solve_wit_13 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd nx tlst )) (PreH25 : (NxtRange i_4 nx )) (PreH26 : (ArcToRange n_pre i_4 tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg ( &( "to_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z)))))) ((cons ((Znth i_4 edge_u 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 ((2 * i_4 ) + 1 ) (app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) ((2 * i_4 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (i_4 < m_pre) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i_4) ” 
  &&  “ (i_4 <= m_pre) ” 
  &&  “ ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre))) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * i_4 )) ” 
  &&  “ ((Zlength (tlst)) = (2 * i_4 )) ” 
  &&  “ (AdjBuild n_pre i_4 tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange i_4 nx ) ” 
  &&  “ (ArcToRange n_pre i_4 tlst ) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (((( &( "nxt_" ) ) + (((2 * i_4 ) + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg ( &( "to_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z)))))) ((cons ((Znth i_4 edge_u 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 ((2 * i_4 ) + 1 ) (app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z))))) )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
.

Definition solver_partial_solve_wit_14 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd nx tlst )) (PreH25 : (NxtRange i_4 nx )) (PreH26 : (ArcToRange n_pre i_4 tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.seg ( &( "nxt_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z)))))) ((cons ((Znth ((Znth i_4 edge_v 0) - 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg ( &( "to_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z)))))) ((cons ((Znth i_4 edge_u 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (i_4 < m_pre) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i_4) ” 
  &&  “ (i_4 <= m_pre) ” 
  &&  “ ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre))) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * i_4 )) ” 
  &&  “ ((Zlength (tlst)) = (2 * i_4 )) ” 
  &&  “ (AdjBuild n_pre i_4 tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange i_4 nx ) ” 
  &&  “ (ArcToRange n_pre i_4 tlst ) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (((ev_pre + (i_4 * sizeof(INT)))) # Int  |-> (Znth i_4 edge_v 0))
  **  (IntArray.missing_i ev_pre i_4 0 m_pre edge_v )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z)))))) ((cons ((Znth ((Znth i_4 edge_v 0) - 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) )
  **  (IntArray.seg ( &( "to_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z)))))) ((cons ((Znth i_4 edge_u 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
.

Definition solver_partial_solve_wit_15 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (dist_before: (@list (@list Z))) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < m_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (0 <= i_4)) (PreH19 : (i_4 <= m_pre)) (PreH20 : ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre)))) (PreH21 : ((Zlength (hd)) = n_pre)) (PreH22 : ((Zlength (nx)) = (2 * i_4 ))) (PreH23 : ((Zlength (tlst)) = (2 * i_4 ))) (PreH24 : (AdjBuild n_pre i_4 tree_edges hd nx tlst )) (PreH25 : (NxtRange i_4 nx )) (PreH26 : (ArcToRange n_pre i_4 tlst )) (PreH27 : ((Zlength (dist_before)) = 105)) (PreH28 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005))) ,
  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z)))))) ((cons ((Znth ((Znth i_4 edge_v 0) - 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) )
  **  (IntArray.seg ( &( "to_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z)))))) ((cons ((Znth i_4 edge_u 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
|--
  “ (i_4 < m_pre) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= i_4) ” 
  &&  “ (i_4 <= m_pre) ” 
  &&  “ ((i_4 < m_pre) -> ((((1 <= (Znth i_4 edge_u 0)) /\ ((Znth i_4 edge_u 0) <= n_pre)) /\ (1 <= (Znth i_4 edge_v 0))) /\ ((Znth i_4 edge_v 0) <= n_pre))) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * i_4 )) ” 
  &&  “ ((Zlength (tlst)) = (2 * i_4 )) ” 
  &&  “ (AdjBuild n_pre i_4 tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange i_4 nx ) ” 
  &&  “ (ArcToRange n_pre i_4 tlst ) ” 
  &&  “ ((Zlength (dist_before)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc dist_before __default__List_Z))) = 100005)) ”
  &&  (((( &( "head_" ) ) + ((Znth i_4 edge_v 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "head_" ) ) (Znth i_4 edge_v 0) 1 (n_pre + 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (IntArray.seg ( &( "nxt_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (nx) ((cons ((Znth ((Znth i_4 edge_u 0) - 1 ) hd 0)) ((@nil Z)))))) ((cons ((Znth ((Znth i_4 edge_v 0) - 1 ) (replace_Znth (((Znth i_4 edge_u 0) - 1 )) ((2 * i_4 )) (hd)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "nxt_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.seg ( &( "to_" ) ) 0 (((2 * i_4 ) + 1 ) + 1 ) (app ((app (tlst) ((cons ((Znth i_4 edge_v 0)) ((@nil Z)))))) ((cons ((Znth i_4 edge_u 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "to_" ) ) (((2 * i_4 ) + 1 ) + 1 ) (2 * m_pre ) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 dist_before )
.

Definition solver_partial_solve_wit_16_pure := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd: (@list Z)) (nx: (@list Z)) (tlst: (@list Z)) (rows: (@list (@list Z))) (c: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (Pre k_pre s_pre tree_edges goods )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (1 <= s_pre)) (PreH7 : (s_pre <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (k_pre <= n_pre)) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH12 : (n_pre = (Zlength (goods)))) (PreH13 : (m_pre = (Zlength (tree_edges)))) (PreH14 : ((Zlength (edge_u)) = m_pre)) (PreH15 : ((Zlength (edge_v)) = m_pre)) (PreH16 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH17 : (1 <= c)) (PreH18 : (c <= k_pre)) (PreH19 : ((Zlength (hd)) = n_pre)) (PreH20 : ((Zlength (nx)) = (2 * m_pre ))) (PreH21 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH22 : (AdjBuild n_pre m_pre tree_edges hd nx tlst )) (PreH23 : (NxtRange m_pre nx )) (PreH24 : (ArcToRange n_pre m_pre tlst )) (PreH25 : ((Zlength (rows)) = 105)) (PreH26 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH27 : (BfsRows n_pre tree_edges goods rows c )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.missing_i ( &( "dist_" ) ) c 0 105 100005 rows )
  **  (IntArray.full ((( &( "dist_" ) ) + (c * (sizeof(INT) * 100005))) + (0 * sizeof(INT))) 100005 (Znth c rows __default__List_Z) )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= c) ” 
  &&  “ (c <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ (AdjBuild n_pre m_pre tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange m_pre nx ) ” 
  &&  “ (ArcToRange n_pre m_pre tlst ) ” 
  &&  “ ((Zlength ((Znth c rows __default__List_Z))) = 100005) ”
.

Definition solver_partial_solve_wit_16_aux := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd: (@list Z)) (nx: (@list Z)) (tlst: (@list Z)) (rows: (@list (@list Z))) (c: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (Pre k_pre s_pre tree_edges goods )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (1 <= s_pre)) (PreH7 : (s_pre <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (k_pre <= n_pre)) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH12 : (n_pre = (Zlength (goods)))) (PreH13 : (m_pre = (Zlength (tree_edges)))) (PreH14 : ((Zlength (edge_u)) = m_pre)) (PreH15 : ((Zlength (edge_v)) = m_pre)) (PreH16 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH17 : (1 <= c)) (PreH18 : (c <= k_pre)) (PreH19 : ((Zlength (hd)) = n_pre)) (PreH20 : ((Zlength (nx)) = (2 * m_pre ))) (PreH21 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH22 : (AdjBuild n_pre m_pre tree_edges hd nx tlst )) (PreH23 : (NxtRange m_pre nx )) (PreH24 : (ArcToRange n_pre m_pre tlst )) (PreH25 : ((Zlength (rows)) = 105)) (PreH26 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH27 : (BfsRows n_pre tree_edges goods rows c )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.missing_i ( &( "dist_" ) ) c 0 105 100005 rows )
  **  (IntArray.full ((( &( "dist_" ) ) + (c * (sizeof(INT) * 100005))) + (0 * sizeof(INT))) 100005 (Znth c rows __default__List_Z) )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= c) ” 
  &&  “ (c <= 100) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ (AdjBuild n_pre m_pre tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange m_pre nx ) ” 
  &&  “ (ArcToRange n_pre m_pre tlst ) ” 
  &&  “ ((Zlength ((Znth c rows __default__List_Z))) = 100005) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= c) ” 
  &&  “ (c <= k_pre) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst)) = (2 * m_pre )) ” 
  &&  “ (AdjBuild n_pre m_pre tree_edges hd nx tlst ) ” 
  &&  “ (NxtRange m_pre nx ) ” 
  &&  “ (ArcToRange n_pre m_pre tlst ) ” 
  &&  “ ((Zlength (rows)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows c ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full ((( &( "dist_" ) ) + (c * (sizeof(INT) * 100005))) + (0 * sizeof(INT))) 100005 (Znth c rows __default__List_Z) )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.undef_seg cost_pre 1 (n_pre + 1 ) )
  **  (IntArray.undef_full ( &( "tmp_" ) ) k_pre )
  **  (IntArray2.missing_i ( &( "dist_" ) ) c 0 105 100005 rows )
.

Definition solver_partial_solve_wit_16 := solver_partial_solve_wit_16_pure -> solver_partial_solve_wit_16_aux.

Definition solver_partial_solve_wit_17 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tp: (@list Z)) (rows: (@list (@list Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (c: Z) (out: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c <= k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out)) = (v - 1 ))) (PreH21 : (1 <= c)) (PreH22 : (c <= (k_pre + 1 ))) (PreH23 : ((Zlength (hd)) = n_pre)) (PreH24 : ((Zlength (nx)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows)) = 105)) (PreH27 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) (PreH30 : ((Zlength (tp)) = (c - 1 ))) (PreH31 : (TmpPrefix n_pre tree_edges goods v tp (c - 1 ) )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.seg ( &( "tmp_" ) ) 0 (c - 1 ) tp )
  **  (IntArray.undef_seg ( &( "tmp_" ) ) (c - 1 ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  “ (c <= k_pre) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ ((Zlength (out)) = (v - 1 )) ” 
  &&  “ (1 <= c) ” 
  &&  “ (c <= (k_pre + 1 )) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (rows)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) ) ” 
  &&  “ (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) ) ” 
  &&  “ ((Zlength (tp)) = (c - 1 )) ” 
  &&  “ (TmpPrefix n_pre tree_edges goods v tp (c - 1 ) ) ”
  &&  ((((( &( "dist_" ) ) + (c * (sizeof(INT) * 100005))) + (v * sizeof(INT)))) # Int  |-> (Znth (v) ((Znth c rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (( &( "dist_" ) ) + (c * (sizeof(INT) * 100005))) v 0 100005 (Znth c rows __default__List_Z) )
  **  (IntArray2.missing_i ( &( "dist_" ) ) c 0 105 100005 rows )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.seg ( &( "tmp_" ) ) 0 (c - 1 ) tp )
  **  (IntArray.undef_seg ( &( "tmp_" ) ) (c - 1 ) k_pre )
.

Definition solver_partial_solve_wit_18 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (tp: (@list Z)) (rows: (@list (@list Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (c: Z) (out: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (c <= k_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out)) = (v - 1 ))) (PreH21 : (1 <= c)) (PreH22 : (c <= (k_pre + 1 ))) (PreH23 : ((Zlength (hd)) = n_pre)) (PreH24 : ((Zlength (nx)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows)) = 105)) (PreH27 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) (PreH30 : ((Zlength (tp)) = (c - 1 ))) (PreH31 : (TmpPrefix n_pre tree_edges goods v tp (c - 1 ) )) ,
  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.seg ( &( "tmp_" ) ) 0 (c - 1 ) tp )
  **  (IntArray.undef_seg ( &( "tmp_" ) ) (c - 1 ) k_pre )
|--
  “ (c <= k_pre) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ ((Zlength (out)) = (v - 1 )) ” 
  &&  “ (1 <= c) ” 
  &&  “ (c <= (k_pre + 1 )) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (rows)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) ) ” 
  &&  “ (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) ) ” 
  &&  “ ((Zlength (tp)) = (c - 1 )) ” 
  &&  “ (TmpPrefix n_pre tree_edges goods v tp (c - 1 ) ) ”
  &&  (((( &( "tmp_" ) ) + ((c - 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "tmp_" ) ) ((c - 1 ) + 1 ) k_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.seg ( &( "tmp_" ) ) 0 (c - 1 ) tp )
.

Definition solver_partial_solve_wit_19_pure := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd: (@list Z)) (nx: (@list Z)) (tlst: (@list Z)) (rows: (@list (@list Z))) (out: (@list Z)) (tp: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (Pre k_pre s_pre tree_edges goods )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (1 <= s_pre)) (PreH7 : (s_pre <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (k_pre <= n_pre)) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH12 : (n_pre = (Zlength (goods)))) (PreH13 : (m_pre = (Zlength (tree_edges)))) (PreH14 : ((Zlength (edge_u)) = m_pre)) (PreH15 : ((Zlength (edge_v)) = m_pre)) (PreH16 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH17 : (1 <= v)) (PreH18 : (v <= n_pre)) (PreH19 : ((Zlength (out)) = (v - 1 ))) (PreH20 : ((Zlength (hd)) = n_pre)) (PreH21 : ((Zlength (nx)) = (2 * m_pre ))) (PreH22 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH23 : ((Zlength (rows)) = 105)) (PreH24 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH25 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH26 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) (PreH27 : (TmpPrefix n_pre tree_edges goods v tp k_pre )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Int  |-> s_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "cost" ) )) # Ptr  |-> cost_pre)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full (( &( "tmp_" ) ) + (0 * sizeof(INT))) k_pre tp )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= INT_MAX) ”
.

Definition solver_partial_solve_wit_19_aux := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (hd: (@list Z)) (nx: (@list Z)) (tlst: (@list Z)) (rows: (@list (@list Z))) (out: (@list Z)) (tp: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (Pre k_pre s_pre tree_edges goods )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (0 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (1 <= s_pre)) (PreH7 : (s_pre <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (k_pre <= n_pre)) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH12 : (n_pre = (Zlength (goods)))) (PreH13 : (m_pre = (Zlength (tree_edges)))) (PreH14 : ((Zlength (edge_u)) = m_pre)) (PreH15 : ((Zlength (edge_v)) = m_pre)) (PreH16 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH17 : (1 <= v)) (PreH18 : (v <= n_pre)) (PreH19 : ((Zlength (out)) = (v - 1 ))) (PreH20 : ((Zlength (hd)) = n_pre)) (PreH21 : ((Zlength (nx)) = (2 * m_pre ))) (PreH22 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH23 : ((Zlength (rows)) = 105)) (PreH24 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH25 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH26 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) (PreH27 : (TmpPrefix n_pre tree_edges goods v tp k_pre )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full (( &( "tmp_" ) ) + (0 * sizeof(INT))) k_pre tp )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ ((Zlength (out)) = (v - 1 )) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (rows)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) ) ” 
  &&  “ (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) ) ” 
  &&  “ (TmpPrefix n_pre tree_edges goods v tp k_pre ) ”
  &&  (IntArray.full (( &( "tmp_" ) ) + (0 * sizeof(INT))) k_pre tp )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
.

Definition solver_partial_solve_wit_19 := solver_partial_solve_wit_19_pure -> solver_partial_solve_wit_19_aux.

Definition solver_partial_solve_wit_20 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (sum: Z) (tp0: (@list Z)) (l1: (@list Z)) (rows: (@list (@list Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z) (out: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 < s_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out)) = (v - 1 ))) (PreH21 : (0 <= i_4)) (PreH22 : (i_4 <= s_pre)) (PreH23 : ((Zlength (hd)) = n_pre)) (PreH24 : ((Zlength (nx)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows)) = 105)) (PreH27 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) (PreH30 : ((Zlength (l1)) = k_pre)) (PreH31 : (mono_nondec l1 )) (PreH32 : ((Zlength (tp0)) = k_pre)) (PreH33 : (TmpPrefix n_pre tree_edges goods v tp0 k_pre )) (PreH34 : (Permutation tp0 l1 )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 ))))) (PreH36 : (sum = (ZSum ((sublist (0) (i_4) (l1)))))) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full ( &( "tmp_" ) ) k_pre l1 )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  “ (i_4 < s_pre) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ ((Zlength (out)) = (v - 1 )) ” 
  &&  “ (0 <= i_4) ” 
  &&  “ (i_4 <= s_pre) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (rows)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) ) ” 
  &&  “ (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) ) ” 
  &&  “ ((Zlength (l1)) = k_pre) ” 
  &&  “ (mono_nondec l1 ) ” 
  &&  “ ((Zlength (tp0)) = k_pre) ” 
  &&  “ (TmpPrefix n_pre tree_edges goods v tp0 k_pre ) ” 
  &&  “ (Permutation tp0 l1 ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 )))) ” 
  &&  “ (sum = (ZSum ((sublist (0) (i_4) (l1))))) ”
  &&  (((( &( "tmp_" ) ) + (i_4 * sizeof(INT)))) # Int  |-> (Znth i_4 l1 0))
  **  (IntArray.missing_i ( &( "tmp_" ) ) i_4 0 k_pre l1 )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
.

Definition solver_partial_solve_wit_21 := 
forall (cost_pre: Z) (ev_pre: Z) (eu_pre: Z) (a_pre: Z) (s_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (edge_v: (@list Z)) (edge_u: (@list Z)) (goods: (@list Z)) (tree_edges: (@list (Z * Z))) (sum: Z) (tp0: (@list Z)) (l1: (@list Z)) (rows: (@list (@list Z))) (tlst: (@list Z)) (nx: (@list Z)) (hd: (@list Z)) (i_4: Z) (out: (@list Z)) (v: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i_4 >= s_pre)) (PreH2 : (Pre k_pre s_pre tree_edges goods )) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (0 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (1 <= s_pre)) (PreH8 : (s_pre <= k_pre)) (PreH9 : (k_pre <= 100)) (PreH10 : (k_pre <= n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre)))) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))))) (PreH13 : (n_pre = (Zlength (goods)))) (PreH14 : (m_pre = (Zlength (tree_edges)))) (PreH15 : ((Zlength (edge_u)) = m_pre)) (PreH16 : ((Zlength (edge_v)) = m_pre)) (PreH17 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z))))))) (PreH18 : (1 <= v)) (PreH19 : (v <= n_pre)) (PreH20 : ((Zlength (out)) = (v - 1 ))) (PreH21 : (0 <= i_4)) (PreH22 : (i_4 <= s_pre)) (PreH23 : ((Zlength (hd)) = n_pre)) (PreH24 : ((Zlength (nx)) = (2 * m_pre ))) (PreH25 : ((Zlength (tlst)) = (2 * m_pre ))) (PreH26 : ((Zlength (rows)) = 105)) (PreH27 : forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005))) (PreH28 : (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) )) (PreH29 : (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) )) (PreH30 : ((Zlength (l1)) = k_pre)) (PreH31 : (mono_nondec l1 )) (PreH32 : ((Zlength (tp0)) = k_pre)) (PreH33 : (TmpPrefix n_pre tree_edges goods v tp0 k_pre )) (PreH34 : (Permutation tp0 l1 )) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 ))))) (PreH36 : (sum = (ZSum ((sublist (0) (i_4) (l1)))))) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (Int64Array.undef_seg cost_pre v (n_pre + 1 ) )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full ( &( "tmp_" ) ) k_pre l1 )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
|--
  “ (i_4 >= s_pre) ” 
  &&  “ (Pre k_pre s_pre tree_edges goods ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (1 <= s_pre) ” 
  &&  “ (s_pre <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i goods 0)) /\ ((Znth i goods 0) <= k_pre))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> (((((1 <= (fst ((Znth i_2 tree_edges __default__Prod_Z_Z)))) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ (1 <= (snd ((Znth i_2 tree_edges __default__Prod_Z_Z))))) /\ ((snd ((Znth i_2 tree_edges __default__Prod_Z_Z))) <= n_pre)) /\ ((fst ((Znth i_2 tree_edges __default__Prod_Z_Z))) <> (snd ((Znth i_2 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (n_pre = (Zlength (goods))) ” 
  &&  “ (m_pre = (Zlength (tree_edges))) ” 
  &&  “ ((Zlength (edge_u)) = m_pre) ” 
  &&  “ ((Zlength (edge_v)) = m_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < m_pre)) -> (((Znth i_3 edge_u 0) = (fst ((Znth i_3 tree_edges __default__Prod_Z_Z)))) /\ ((Znth i_3 edge_v 0) = (snd ((Znth i_3 tree_edges __default__Prod_Z_Z)))))) ” 
  &&  “ (1 <= v) ” 
  &&  “ (v <= n_pre) ” 
  &&  “ ((Zlength (out)) = (v - 1 )) ” 
  &&  “ (0 <= i_4) ” 
  &&  “ (i_4 <= s_pre) ” 
  &&  “ ((Zlength (hd)) = n_pre) ” 
  &&  “ ((Zlength (nx)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (tlst)) = (2 * m_pre )) ” 
  &&  “ ((Zlength (rows)) = 105) ” 
  &&  “ forall (cc: Z) , (((0 <= cc) /\ (cc < 105)) -> ((Zlength ((Znth cc rows __default__List_Z))) = 100005)) ” 
  &&  “ (BfsRows n_pre tree_edges goods rows (k_pre + 1 ) ) ” 
  &&  “ (OutPrefix n_pre s_pre tree_edges goods out (v - 1 ) ) ” 
  &&  “ ((Zlength (l1)) = k_pre) ” 
  &&  “ (mono_nondec l1 ) ” 
  &&  “ ((Zlength (tp0)) = k_pre) ” 
  &&  “ (TmpPrefix n_pre tree_edges goods v tp0 k_pre ) ” 
  &&  “ (Permutation tp0 l1 ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < k_pre)) -> ((0 <= (Znth j l1 0)) /\ ((Znth j l1 0) <= (n_pre - 1 )))) ” 
  &&  “ (sum = (ZSum ((sublist (0) (i_4) (l1))))) ”
  &&  (((cost_pre + (v * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg cost_pre (v + 1 ) (n_pre + 1 ) )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) goods )
  **  (IntArray.full eu_pre m_pre edge_u )
  **  (IntArray.full ev_pre m_pre edge_v )
  **  (Int64Array.seg cost_pre 1 v out )
  **  (IntArray.seg ( &( "head_" ) ) 1 (n_pre + 1 ) hd )
  **  (IntArray.full ( &( "nxt_" ) ) (2 * m_pre ) nx )
  **  (IntArray.full ( &( "to_" ) ) (2 * m_pre ) tlst )
  **  (IntArray.undef_full ( &( "queue_" ) ) n_pre )
  **  (IntArray.full ( &( "tmp_" ) ) k_pre l1 )
  **  (IntArray2.full ( &( "dist_" ) ) 105 100005 rows )
.

Module Type VC_Correct.

Include array2_Strategy_Correct.
Include array2_char_Strategy_Correct.
Include int_array_Strategy_Correct.
Include char_array_Strategy_Correct.
Include array2_ext_Strategy_Correct.

Axiom proof_of_bfs_type_safety_wit_1 : bfs_type_safety_wit_1.
Axiom proof_of_bfs_type_safety_wit_2 : bfs_type_safety_wit_2.
Axiom proof_of_bfs_type_safety_wit_3 : bfs_type_safety_wit_3.
Axiom proof_of_bfs_type_safety_wit_4 : bfs_type_safety_wit_4.
Axiom proof_of_bfs_type_safety_wit_5 : bfs_type_safety_wit_5.
Axiom proof_of_bfs_type_safety_wit_6 : bfs_type_safety_wit_6.
Axiom proof_of_bfs_type_safety_wit_7 : bfs_type_safety_wit_7.
Axiom proof_of_bfs_type_safety_wit_8 : bfs_type_safety_wit_8.
Axiom proof_of_bfs_type_safety_wit_9 : bfs_type_safety_wit_9.
Axiom proof_of_bfs_type_safety_wit_10 : bfs_type_safety_wit_10.
Axiom proof_of_bfs_type_safety_wit_11 : bfs_type_safety_wit_11.
Axiom proof_of_bfs_type_safety_wit_12 : bfs_type_safety_wit_12.
Axiom proof_of_bfs_type_safety_wit_13 : bfs_type_safety_wit_13.
Axiom proof_of_bfs_type_safety_wit_14 : bfs_type_safety_wit_14.
Axiom proof_of_bfs_type_safety_wit_15 : bfs_type_safety_wit_15.
Axiom proof_of_bfs_type_safety_wit_16 : bfs_type_safety_wit_16.
Axiom proof_of_bfs_type_safety_wit_17 : bfs_type_safety_wit_17.
Axiom proof_of_bfs_type_safety_wit_18 : bfs_type_safety_wit_18.
Axiom proof_of_bfs_type_safety_wit_19 : bfs_type_safety_wit_19.
Axiom proof_of_bfs_type_safety_wit_20 : bfs_type_safety_wit_20.
Axiom proof_of_bfs_type_safety_wit_21 : bfs_type_safety_wit_21.
Axiom proof_of_bfs_type_entail_wit_1 : bfs_type_entail_wit_1.
Axiom proof_of_bfs_type_entail_wit_2 : bfs_type_entail_wit_2.
Axiom proof_of_bfs_type_entail_wit_3 : bfs_type_entail_wit_3.
Axiom proof_of_bfs_type_entail_wit_4_1 : bfs_type_entail_wit_4_1.
Axiom proof_of_bfs_type_entail_wit_4_2 : bfs_type_entail_wit_4_2.
Axiom proof_of_bfs_type_entail_wit_5 : bfs_type_entail_wit_5.
Axiom proof_of_bfs_type_entail_wit_6 : bfs_type_entail_wit_6.
Axiom proof_of_bfs_type_entail_wit_7 : bfs_type_entail_wit_7.
Axiom proof_of_bfs_type_entail_wit_8_1 : bfs_type_entail_wit_8_1.
Axiom proof_of_bfs_type_entail_wit_8_2 : bfs_type_entail_wit_8_2.
Axiom proof_of_bfs_type_entail_wit_9 : bfs_type_entail_wit_9.
Axiom proof_of_bfs_type_return_wit_1 : bfs_type_return_wit_1.
Axiom proof_of_bfs_type_partial_solve_wit_1 : bfs_type_partial_solve_wit_1.
Axiom proof_of_bfs_type_partial_solve_wit_2 : bfs_type_partial_solve_wit_2.
Axiom proof_of_bfs_type_partial_solve_wit_3 : bfs_type_partial_solve_wit_3.
Axiom proof_of_bfs_type_partial_solve_wit_4 : bfs_type_partial_solve_wit_4.
Axiom proof_of_bfs_type_partial_solve_wit_5 : bfs_type_partial_solve_wit_5.
Axiom proof_of_bfs_type_partial_solve_wit_6 : bfs_type_partial_solve_wit_6.
Axiom proof_of_bfs_type_partial_solve_wit_7 : bfs_type_partial_solve_wit_7.
Axiom proof_of_bfs_type_partial_solve_wit_8 : bfs_type_partial_solve_wit_8.
Axiom proof_of_bfs_type_partial_solve_wit_9 : bfs_type_partial_solve_wit_9.
Axiom proof_of_bfs_type_partial_solve_wit_10 : bfs_type_partial_solve_wit_10.
Axiom proof_of_bfs_type_partial_solve_wit_11 : bfs_type_partial_solve_wit_11.
Axiom proof_of_bfs_type_partial_solve_wit_12 : bfs_type_partial_solve_wit_12.
Axiom proof_of_bfs_type_partial_solve_wit_13 : bfs_type_partial_solve_wit_13.
Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Axiom proof_of_solver_safety_wit_8 : solver_safety_wit_8.
Axiom proof_of_solver_safety_wit_9 : solver_safety_wit_9.
Axiom proof_of_solver_safety_wit_10 : solver_safety_wit_10.
Axiom proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Axiom proof_of_solver_safety_wit_12 : solver_safety_wit_12.
Axiom proof_of_solver_safety_wit_13 : solver_safety_wit_13.
Axiom proof_of_solver_safety_wit_14 : solver_safety_wit_14.
Axiom proof_of_solver_safety_wit_15 : solver_safety_wit_15.
Axiom proof_of_solver_safety_wit_16 : solver_safety_wit_16.
Axiom proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Axiom proof_of_solver_safety_wit_18 : solver_safety_wit_18.
Axiom proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Axiom proof_of_solver_safety_wit_20 : solver_safety_wit_20.
Axiom proof_of_solver_safety_wit_21 : solver_safety_wit_21.
Axiom proof_of_solver_safety_wit_22 : solver_safety_wit_22.
Axiom proof_of_solver_safety_wit_23 : solver_safety_wit_23.
Axiom proof_of_solver_safety_wit_24 : solver_safety_wit_24.
Axiom proof_of_solver_safety_wit_25 : solver_safety_wit_25.
Axiom proof_of_solver_safety_wit_26 : solver_safety_wit_26.
Axiom proof_of_solver_safety_wit_27 : solver_safety_wit_27.
Axiom proof_of_solver_safety_wit_28 : solver_safety_wit_28.
Axiom proof_of_solver_safety_wit_29 : solver_safety_wit_29.
Axiom proof_of_solver_safety_wit_30 : solver_safety_wit_30.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Axiom proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Axiom proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Axiom proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Axiom proof_of_solver_entail_wit_14 : solver_entail_wit_14.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.
Axiom proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13.
Axiom proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14.
Axiom proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15.
Axiom proof_of_solver_partial_solve_wit_16_pure : solver_partial_solve_wit_16_pure.
Axiom proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16.
Axiom proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17.
Axiom proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18.
Axiom proof_of_solver_partial_solve_wit_19_pure : solver_partial_solve_wit_19_pure.
Axiom proof_of_solver_partial_solve_wit_19 : solver_partial_solve_wit_19.
Axiom proof_of_solver_partial_solve_wit_20 : solver_partial_solve_wit_20.
Axiom proof_of_solver_partial_solve_wit_21 : solver_partial_solve_wit_21.

End VC_Correct.
