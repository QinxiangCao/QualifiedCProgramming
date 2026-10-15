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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P049_411B_multi_core_processor_lib.
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

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < (n_pre * m_pre ))) -> ((0 <= (Znth j (concat (ins)) 0)) /\ ((Znth j (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Zlength ((Znth i ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Zlength ((Znth i_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth i_2 xrows __default__List_Z))) = (Znth i_2 ins __default__List_Z))))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
  **  (IntArray.undef_full ( &( "writers" ) ) 105 )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 (repeat_Z (0) (105)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.undef_full lock_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) ,
  (IntArray.seg lock_pre 0 (i + 1 ) (app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg lock_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 (repeat_Z (0) (105)) )
  **  (IntArray.undef_full ( &( "writers" ) ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_3 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.seg lock_pre 0 i (repeat_Z (0) (i)) )
  **  (IntArray.undef_seg lock_pre i n_pre )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 (repeat_Z (0) (105)) )
  **  (IntArray.undef_full ( &( "writers" ) ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.seg lock_pre 0 i (repeat_Z (0) (i)) )
  **  (IntArray.undef_seg lock_pre i n_pre )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 (repeat_Z (0) (105)) )
  **  (IntArray.undef_full ( &( "writers" ) ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (locks: (@list Z)) (dead: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH13 : (0 <= j)) (PreH14 : (j < m_pre)) (PreH15 : (LockTimesThrough ins locks j )) (PreH16 : (DeadCellsThrough ins locks k_pre j dead )) (PreH17 : (aligned_4 (( &( "writers" ) ) + (0 * sizeof(INT))) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (UCharArray.undef_full (( &( "writers" ) ) + (0 * sizeof(INT))) (sizeof(INT) * (k_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  “ ((k_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k_pre + 1 )) ”
.

Definition solver_safety_wit_6 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (locks: (@list Z)) (dead: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH13 : (0 <= j)) (PreH14 : (j < m_pre)) (PreH15 : (LockTimesThrough ins locks j )) (PreH16 : (DeadCellsThrough ins locks k_pre j dead )) (PreH17 : (aligned_4 (( &( "writers" ) ) + (0 * sizeof(INT))) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (UCharArray.undef_full (( &( "writers" ) ) + (0 * sizeof(INT))) (sizeof(INT) * (k_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (locks: (@list Z)) (dead: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH13 : (0 <= j)) (PreH14 : (j < m_pre)) (PreH15 : (LockTimesThrough ins locks j )) (PreH16 : (DeadCellsThrough ins locks k_pre j dead )) (PreH17 : (aligned_4 (( &( "writers" ) ) + (0 * sizeof(INT))) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (UCharArray.undef_full (( &( "writers" ) ) + (0 * sizeof(INT))) (sizeof(INT) * (k_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (locks: (@list Z)) (dead: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH13 : (0 <= j)) (PreH14 : (j < m_pre)) (PreH15 : (LockTimesThrough ins locks j )) (PreH16 : (DeadCellsThrough ins locks k_pre j dead )) (PreH17 : (aligned_4 (( &( "writers" ) ) + (0 * sizeof(INT))) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (UCharArray.undef_full (( &( "writers" ) ) + (0 * sizeof(INT))) (sizeof(INT) * (k_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (locks: (@list Z)) (dead: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH13 : (0 <= j)) (PreH14 : (j < m_pre)) (PreH15 : (LockTimesThrough ins locks j )) (PreH16 : (DeadCellsThrough ins locks k_pre j dead )) ,
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) (repeat_Z (0) ((k_pre + 1 ))) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead: (@list Z)) (locks: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c <= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (LockTimesThrough ins locks j )) (PreH19 : (DeadCellsThrough ins locks k_pre j dead )) ,
  (IntArray.seg ( &( "first" ) ) 1 (c + 1 ) (app ((repeat_Z ((-1)) ((c - 1 )))) ((cons ((-1)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "first" ) ) (c + 1 ) 105 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) (repeat_Z (0) ((k_pre + 1 ))) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
|--
  “ ((c + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c + 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead: (@list Z)) (locks: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c <= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (LockTimesThrough ins locks j )) (PreH19 : (DeadCellsThrough ins locks k_pre j dead )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) (repeat_Z (0) ((k_pre + 1 ))) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 c (repeat_Z ((-1)) ((c - 1 ))) )
  **  (IntArray.undef_seg ( &( "first" ) ) c 105 )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_12 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead: (@list Z)) (locks: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c <= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (LockTimesThrough ins locks j )) (PreH19 : (DeadCellsThrough ins locks k_pre j dead )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) (repeat_Z (0) ((k_pre + 1 ))) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 c (repeat_Z ((-1)) ((c - 1 ))) )
  **  (IntArray.undef_seg ( &( "first" ) ) c 105 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_13 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead: (@list Z)) (locks: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c > k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (LockTimesThrough ins locks j )) (PreH19 : (DeadCellsThrough ins locks k_pre j dead )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) (repeat_Z (0) ((k_pre + 1 ))) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 c (repeat_Z ((-1)) ((c - 1 ))) )
  **  (IntArray.undef_seg ( &( "first" ) ) c 105 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_14 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth i locks 0) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH20 : (DirectLockScan ins locks (j + 1 ) i )) (PreH21 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_15 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH4 : ((Znth i locks 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (Pre k_pre ins )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH14 : (n_pre = (Zlength (ins)))) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH16 : ((Zlength (xrows)) = n_pre)) (PreH17 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH18 : (0 <= j)) (PreH19 : (j < m_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH23 : (DirectLockScan ins locks (j + 1 ) i )) (PreH24 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) (PreH25 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) <> 0)) ,
  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  ((( &( "c" ) )) # Int  |-> (Znth (j) ((Znth i xrows __default__List_Z)) (0)))
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_16 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH4 : ((Znth i locks 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (Pre k_pre ins )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH14 : (n_pre = (Zlength (ins)))) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH16 : ((Zlength (xrows)) = n_pre)) (PreH17 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH18 : (0 <= j)) (PreH19 : (j < m_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH23 : (DirectLockScan ins locks (j + 1 ) i )) (PreH24 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) (PreH25 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) <> 0)) ,
  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  ((( &( "c" ) )) # Int  |-> (Znth (j) ((Znth i xrows __default__List_Z)) (0)))
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_17 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH4 : ((Znth i locks 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (Pre k_pre ins )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH14 : (n_pre = (Zlength (ins)))) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH16 : ((Zlength (xrows)) = n_pre)) (PreH17 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH18 : (0 <= j)) (PreH19 : (j < m_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH23 : (DirectLockScan ins locks (j + 1 ) i )) (PreH24 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) (PreH25 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) = 0)) ,
  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  ((( &( "c" ) )) # Int  |-> (Znth (j) ((Znth i xrows __default__List_Z)) (0)))
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 0 ) counts 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 0 ) counts 0) + 1 )) ”
) \/
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH4 : ((Znth i locks 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (Pre k_pre ins )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH14 : (n_pre = (Zlength (ins)))) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH16 : ((Zlength (xrows)) = n_pre)) (PreH17 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH18 : (0 <= j)) (PreH19 : (j < m_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH23 : (DirectLockScan ins locks (j + 1 ) i )) (PreH24 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) (PreH25 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) = 0)) ,
  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  ((( &( "c" ) )) # Int  |-> (Znth (j) ((Znth i xrows __default__List_Z)) (0)))
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 0 ) counts 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 0 ) counts 0) + 1 )) ”
).

Definition solver_safety_wit_17_split_goal_1 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH4 : ((Znth i locks 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (Pre k_pre ins )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH14 : (n_pre = (Zlength (ins)))) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH16 : ((Zlength (xrows)) = n_pre)) (PreH17 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH18 : (0 <= j)) (PreH19 : (j < m_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH23 : (DirectLockScan ins locks (j + 1 ) i )) (PreH24 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) (PreH25 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) = 0)) ,
  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  ((( &( "c" ) )) # Int  |-> (Znth (j) ((Znth i xrows __default__List_Z)) (0)))
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 0 ) counts 0) + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_17_split_goal_2 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH4 : ((Znth i locks 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (Pre k_pre ins )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH14 : (n_pre = (Zlength (ins)))) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH16 : ((Zlength (xrows)) = n_pre)) (PreH17 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH18 : (0 <= j)) (PreH19 : (j < m_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH23 : (DirectLockScan ins locks (j + 1 ) i )) (PreH24 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) (PreH25 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) = 0)) ,
  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  ((( &( "c" ) )) # Int  |-> (Znth (j) ((Znth i xrows __default__List_Z)) (0)))
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ ((INT_MIN) <= ((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 0 ) counts 0) + 1 )) ”
.

Definition solver_safety_wit_18 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH4 : ((Znth i locks 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (Pre k_pre ins )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH14 : (n_pre = (Zlength (ins)))) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH16 : ((Zlength (xrows)) = n_pre)) (PreH17 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH18 : (0 <= j)) (PreH19 : (j < m_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH23 : (DirectLockScan ins locks (j + 1 ) i )) (PreH24 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) (PreH25 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) = 0)) ,
  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  ((( &( "c" ) )) # Int  |-> (Znth (j) ((Znth i xrows __default__List_Z)) (0)))
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_19 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH4 : ((Znth i locks 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (Pre k_pre ins )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH14 : (n_pre = (Zlength (ins)))) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH16 : ((Zlength (xrows)) = n_pre)) (PreH17 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH18 : (0 <= j)) (PreH19 : (j < m_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH23 : (DirectLockScan ins locks (j + 1 ) i )) (PreH24 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) (PreH25 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) = 0)) ,
  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.full ( &( "writers" ) ) (k_pre + 1 ) (replace_Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0))) (((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 0 ) counts 0) + 1 )) (counts)) )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  ((( &( "c" ) )) # Int  |-> (Znth (j) ((Znth i xrows __default__List_Z)) (0)))
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_20 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 1 ) firsts 0) < 0)) (PreH2 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH4 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH5 : ((Znth i locks 0) = 0)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (Pre k_pre ins )) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH15 : (n_pre = (Zlength (ins)))) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH17 : ((Zlength (xrows)) = n_pre)) (PreH18 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH19 : (0 <= j)) (PreH20 : (j < m_pre)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH24 : (DirectLockScan ins locks (j + 1 ) i )) (PreH25 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) (PreH26 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) = 0)) ,
  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) (replace_Znth (((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 1 )) (i) (firsts)) )
  **  (IntArray.full ( &( "writers" ) ) (k_pre + 1 ) (replace_Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0))) (((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 0 ) counts 0) + 1 )) (counts)) )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_21 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 1 ) firsts 0) >= 0)) (PreH2 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH4 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH5 : ((Znth i locks 0) = 0)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (Pre k_pre ins )) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH15 : (n_pre = (Zlength (ins)))) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH17 : ((Zlength (xrows)) = n_pre)) (PreH18 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH19 : (0 <= j)) (PreH20 : (j < m_pre)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH24 : (DirectLockScan ins locks (j + 1 ) i )) (PreH25 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) (PreH26 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) = 0)) ,
  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.full ( &( "writers" ) ) (k_pre + 1 ) (replace_Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0))) (((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 0 ) counts 0) + 1 )) (counts)) )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_22 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth i locks 0) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH20 : (DirectLockScan ins locks (j + 1 ) i )) (PreH21 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) ,
  (IntArray.full lock_pre n_pre locks )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_23 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) = 0)) (PreH2 : ((Znth i locks 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (0 <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH21 : (DirectLockScan ins locks (j + 1 ) i )) (PreH22 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_24 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH4 : ((Znth i locks 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (Pre k_pre ins )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH14 : (n_pre = (Zlength (ins)))) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH16 : ((Zlength (xrows)) = n_pre)) (PreH17 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH18 : (0 <= j)) (PreH19 : (j < m_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH23 : (DirectLockScan ins locks (j + 1 ) i )) (PreH24 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) (PreH25 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) <> 0)) ,
  (IntArray.full lock_pre n_pre (replace_Znth (i) ((j + 1 )) (locks)) )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_25 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH19 : (DirectLockScan ins locks (j + 1 ) i )) (PreH20 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) ,
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_26 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead: (@list Z)) (locks: (@list Z)) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c <= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (WriterCounts ins locks (j + 1 ) n_pre k_pre counts )) (PreH19 : (CellMarksPrefix ins locks counts k_pre (j + 1 ) c dead )) (PreH20 : (CollisionClosurePrefix ins locks counts (j + 1 ) c 0 )) ,
  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_27 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead: (@list Z)) (locks: (@list Z)) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (c - 0 ) counts 0) >= 2)) (PreH2 : (c <= k_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (1 <= c)) (PreH18 : (c <= (k_pre + 1 ))) (PreH19 : (WriterCounts ins locks (j + 1 ) n_pre k_pre counts )) (PreH20 : (CellMarksPrefix ins locks counts k_pre (j + 1 ) c dead )) (PreH21 : (CollisionClosurePrefix ins locks counts (j + 1 ) c 0 )) ,
  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_28 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead: (@list Z)) (locks: (@list Z)) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (c - 0 ) counts 0) >= 2)) (PreH2 : (c <= k_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (1 <= c)) (PreH18 : (c <= (k_pre + 1 ))) (PreH19 : (WriterCounts ins locks (j + 1 ) n_pre k_pre counts )) (PreH20 : (CellMarksPrefix ins locks counts k_pre (j + 1 ) c dead )) (PreH21 : (CollisionClosurePrefix ins locks counts (j + 1 ) c 0 )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full ( &( "cell_locked" ) ) 105 (replace_Znth (c) (1) (dead)) )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_29 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead: (@list Z)) (locks: (@list Z)) (i: Z) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) = c)) (PreH2 : ((Znth i locks 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (1 <= c)) (PreH19 : (c <= k_pre)) (PreH20 : (2 <= (Znth c counts 0))) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (WriterCounts ins locks (j + 1 ) n_pre k_pre counts )) (PreH24 : (CellMarksPrefix ins locks counts k_pre (j + 1 ) (c + 1 ) dead )) (PreH25 : (CollisionClosurePrefix ins locks counts (j + 1 ) c i )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_30 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead: (@list Z)) (locks: (@list Z)) (i: Z) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) = c)) (PreH2 : ((Znth i locks 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (1 <= c)) (PreH19 : (c <= k_pre)) (PreH20 : (2 <= (Znth c counts 0))) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (WriterCounts ins locks (j + 1 ) n_pre k_pre counts )) (PreH24 : (CellMarksPrefix ins locks counts k_pre (j + 1 ) (c + 1 ) dead )) (PreH25 : (CollisionClosurePrefix ins locks counts (j + 1 ) c i )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_31 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead: (@list Z)) (locks: (@list Z)) (i: Z) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) = c)) (PreH2 : ((Znth i locks 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (1 <= c)) (PreH19 : (c <= k_pre)) (PreH20 : (2 <= (Znth c counts 0))) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (WriterCounts ins locks (j + 1 ) n_pre k_pre counts )) (PreH24 : (CellMarksPrefix ins locks counts k_pre (j + 1 ) (c + 1 ) dead )) (PreH25 : (CollisionClosurePrefix ins locks counts (j + 1 ) c i )) ,
  (IntArray.full lock_pre n_pre (replace_Znth (i) ((j + 1 )) (locks)) )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_32 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead: (@list Z)) (locks: (@list Z)) (i: Z) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth i locks 0) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (1 <= c)) (PreH18 : (c <= k_pre)) (PreH19 : (2 <= (Znth c counts 0))) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (WriterCounts ins locks (j + 1 ) n_pre k_pre counts )) (PreH23 : (CellMarksPrefix ins locks counts k_pre (j + 1 ) (c + 1 ) dead )) (PreH24 : (CollisionClosurePrefix ins locks counts (j + 1 ) c i )) ,
  (IntArray.full lock_pre n_pre locks )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_33 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead: (@list Z)) (locks: (@list Z)) (i: Z) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> c)) (PreH2 : ((Znth i locks 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (1 <= c)) (PreH19 : (c <= k_pre)) (PreH20 : (2 <= (Znth c counts 0))) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (WriterCounts ins locks (j + 1 ) n_pre k_pre counts )) (PreH24 : (CellMarksPrefix ins locks counts k_pre (j + 1 ) (c + 1 ) dead )) (PreH25 : (CollisionClosurePrefix ins locks counts (j + 1 ) c i )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_34 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead: (@list Z)) (locks: (@list Z)) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c > k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (WriterCounts ins locks (j + 1 ) n_pre k_pre counts )) (PreH19 : (CellMarksPrefix ins locks counts k_pre (j + 1 ) c dead )) (PreH20 : (CollisionClosurePrefix ins locks counts (j + 1 ) c 0 )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_35 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead: (@list Z)) (locks: (@list Z)) (i: Z) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= k_pre)) (PreH18 : (2 <= (Znth c counts 0))) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (WriterCounts ins locks (j + 1 ) n_pre k_pre counts )) (PreH22 : (CellMarksPrefix ins locks counts k_pre (j + 1 ) (c + 1 ) dead )) (PreH23 : (CollisionClosurePrefix ins locks counts (j + 1 ) c i )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ ((c + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c + 1 )) ”
.

Definition solver_safety_wit_36 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead: (@list Z)) (locks: (@list Z)) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (c - 0 ) counts 0) < 2)) (PreH2 : (c <= k_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (1 <= c)) (PreH18 : (c <= (k_pre + 1 ))) (PreH19 : (WriterCounts ins locks (j + 1 ) n_pre k_pre counts )) (PreH20 : (CellMarksPrefix ins locks counts k_pre (j + 1 ) c dead )) (PreH21 : (CollisionClosurePrefix ins locks counts (j + 1 ) c 0 )) ,
  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ ((c + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < (n_pre * m_pre ))) -> ((0 <= (Znth j (concat (ins)) 0)) /\ ((Znth j (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Zlength ((Znth i ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Zlength ((Znth i_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth i_2 xrows __default__List_Z))) = (Znth i_2 ins __default__List_Z))))) ,
  (IntArray.undef_full ( &( "first" ) ) 105 )
  **  (IntArray.undef_full ( &( "writers" ) ) 105 )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 (repeat_Z (0) (105)) )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.undef_full lock_pre n_pre )
|--
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.seg lock_pre 0 0 (repeat_Z (0) (0)) )
  **  (IntArray.undef_seg lock_pre 0 n_pre )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 (repeat_Z (0) (105)) )
  **  (IntArray.undef_full ( &( "writers" ) ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < (n_pre * m_pre ))) -> ((0 <= (Znth j (concat (ins)) 0)) /\ ((Znth j (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Zlength ((Znth i ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Zlength ((Znth i_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth i_2 xrows __default__List_Z))) = (Znth i_2 ins __default__List_Z))))) ,
  TT && emp 
|--
  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ ((repeat_Z (0) (0)) = (@nil Z)) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < (n_pre * m_pre ))) -> ((0 <= (Znth j (concat (ins)) 0)) /\ ((Znth j (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Zlength ((Znth i ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Zlength ((Znth i_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth i_2 xrows __default__List_Z))) = (Znth i_2 ins __default__List_Z))))) ,
  forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < (n_pre * m_pre ))) -> ((0 <= (Znth j (concat (ins)) 0)) /\ ((Znth j (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Zlength ((Znth i ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Zlength ((Znth i_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth i_2 xrows __default__List_Z))) = (Znth i_2 ins __default__List_Z))))) ,
  forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < (n_pre * m_pre ))) -> ((0 <= (Znth j (concat (ins)) 0)) /\ ((Znth j (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Zlength ((Znth i ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Zlength ((Znth i_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth i_2 xrows __default__List_Z))) = (Znth i_2 ins __default__List_Z))))) ,
  forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))
.

Definition solver_entail_wit_1_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < (n_pre * m_pre ))) -> ((0 <= (Znth j (concat (ins)) 0)) /\ ((Znth j (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Zlength ((Znth i ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((Zlength ((Znth i_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth i_2 xrows __default__List_Z))) = (Znth i_2 ins __default__List_Z))))) ,
  ((repeat_Z (0) (0)) = (@nil Z))
.

Definition solver_entail_wit_2 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) ,
  (IntArray.seg lock_pre 0 (i + 1 ) (app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg lock_pre (i + 1 ) n_pre )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 (repeat_Z (0) (105)) )
  **  (IntArray.undef_full ( &( "writers" ) ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.seg lock_pre 0 (i + 1 ) (repeat_Z (0) ((i + 1 ))) )
  **  (IntArray.undef_seg lock_pre (i + 1 ) n_pre )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 (repeat_Z (0) (105)) )
  **  (IntArray.undef_full ( &( "writers" ) ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) ,
  TT && emp 
|--
  “ ((app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) = (repeat_Z (0) ((i + 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) ,
  ((app ((repeat_Z (0) (i))) ((cons (0) ((@nil Z))))) = (repeat_Z (0) ((i + 1 ))))
.

Definition solver_entail_wit_3 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.seg lock_pre 0 i (repeat_Z (0) (i)) )
  **  (IntArray.undef_seg lock_pre i n_pre )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 (repeat_Z (0) (105)) )
  **  (IntArray.undef_full ( &( "writers" ) ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  EX (dead: (@list Z))  (locks: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (LockTimesThrough ins locks 0 ) ” 
  &&  “ (DeadCellsThrough ins locks k_pre 0 dead ) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.undef_full ( &( "writers" ) ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) ,
  TT && emp 
|--
  “ (DeadCellsThrough ins (repeat_Z (0) (i)) k_pre 0 (repeat_Z (0) (105)) ) ” 
  &&  “ (LockTimesThrough ins (repeat_Z (0) (i)) 0 ) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) ,
  (DeadCellsThrough ins (repeat_Z (0) (i)) k_pre 0 (repeat_Z (0) (105)) )
.

Definition solver_entail_wit_3_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) ,
  (LockTimesThrough ins (repeat_Z (0) (i)) 0 )
.

Definition solver_entail_wit_3_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) ,
  forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))
.

Definition solver_entail_wit_3_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) ,
  forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))
.

Definition solver_entail_wit_3_split_goal_5 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) ,
  forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))
.

Definition solver_entail_wit_4 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (j < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j <= m_pre)) (PreH16 : (LockTimesThrough ins locks_2 j )) (PreH17 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks_2 )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead_2 )
  **  (IntArray.undef_full ( &( "writers" ) ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  EX (dead: (@list Z))  (locks: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (LockTimesThrough ins locks j ) ” 
  &&  “ (DeadCellsThrough ins locks k_pre j dead ) ” 
  &&  “ (aligned_4 (( &( "writers" ) ) + (0 * sizeof(INT))) ) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (UCharArray.undef_full (( &( "writers" ) ) + (0 * sizeof(INT))) (sizeof(INT) * (k_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (j < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j <= m_pre)) (PreH16 : (LockTimesThrough ins locks_2 j )) (PreH17 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) ,
  (IntArray.undef_full ( &( "writers" ) ) 105 )
|--
  “ (aligned_4 (( &( "writers" ) ) + (0 * sizeof(INT))) ) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ”
  &&  (UCharArray.undef_full (( &( "writers" ) ) + (0 * sizeof(INT))) (sizeof(INT) * (k_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (j < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j <= m_pre)) (PreH16 : (LockTimesThrough ins locks_2 j )) (PreH17 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) ,
  (IntArray.undef_full ( &( "writers" ) ) 105 )
|--
  “ (aligned_4 (( &( "writers" ) ) + (0 * sizeof(INT))) ) ”
.

Definition solver_entail_wit_4_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (j < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j <= m_pre)) (PreH16 : (LockTimesThrough ins locks_2 j )) (PreH17 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) ,
  (IntArray.undef_full ( &( "writers" ) ) 105 )
|--
  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ”
.

Definition solver_entail_wit_4_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (j < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j <= m_pre)) (PreH16 : (LockTimesThrough ins locks_2 j )) (PreH17 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) ,
  (IntArray.undef_full ( &( "writers" ) ) 105 )
|--
  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ”
.

Definition solver_entail_wit_4_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (j < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j <= m_pre)) (PreH16 : (LockTimesThrough ins locks_2 j )) (PreH17 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) ,
  (IntArray.undef_full ( &( "writers" ) ) 105 )
|--
  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ”
.

Definition solver_entail_wit_4_split_goal_spatial := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (j < m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j <= m_pre)) (PreH16 : (LockTimesThrough ins locks_2 j )) (PreH17 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) ,
  (IntArray.undef_full ( &( "writers" ) ) 105 )
|--
  (UCharArray.undef_full (( &( "writers" ) ) + (0 * sizeof(INT))) (sizeof(INT) * (k_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
.

Definition solver_entail_wit_5 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (locks_2: (@list Z)) (dead_2: (@list Z)) (j: Z) (retval: Z)  __default__List_Z (PreH1 : (retval = (( &( "writers" ) ) + (0 * sizeof(INT))))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (LockTimesThrough ins locks_2 j )) (PreH17 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) (PreH18 : (aligned_4 (( &( "writers" ) ) + (0 * sizeof(INT))) )) ,
  (UCharArray.full (( &( "writers" ) ) + (0 * sizeof(INT))) (sizeof(INT) * (k_pre + 1 ) ) (repeat_Z (0) ((sizeof(INT) * (k_pre + 1 ) ))) )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks_2 )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead_2 )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  EX (dead: (@list Z))  (locks: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (LockTimesThrough ins locks j ) ” 
  &&  “ (DeadCellsThrough ins locks k_pre j dead ) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) (repeat_Z (0) ((k_pre + 1 ))) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (locks_2: (@list Z)) (dead_2: (@list Z)) (j: Z) (retval: Z)  __default__List_Z (PreH1 : (retval = (( &( "writers" ) ) + (0 * sizeof(INT))))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (LockTimesThrough ins locks_2 j )) (PreH17 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) (PreH18 : (aligned_4 (( &( "writers" ) ) + (0 * sizeof(INT))) )) ,
  (UCharArray.full (( &( "writers" ) ) + (0 * sizeof(INT))) (sizeof(INT) * (k_pre + 1 ) ) (repeat_Z (0) ((sizeof(INT) * (k_pre + 1 ) ))) )
|--
  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ”
  &&  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) (repeat_Z (0) ((k_pre + 1 ))) )
).

Definition solver_entail_wit_5_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (locks_2: (@list Z)) (dead_2: (@list Z)) (j: Z) (retval: Z)  __default__List_Z (PreH1 : (retval = (( &( "writers" ) ) + (0 * sizeof(INT))))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (LockTimesThrough ins locks_2 j )) (PreH17 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) (PreH18 : (aligned_4 (( &( "writers" ) ) + (0 * sizeof(INT))) )) ,
  (UCharArray.full (( &( "writers" ) ) + (0 * sizeof(INT))) (sizeof(INT) * (k_pre + 1 ) ) (repeat_Z (0) ((sizeof(INT) * (k_pre + 1 ) ))) )
|--
  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ”
.

Definition solver_entail_wit_5_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (locks_2: (@list Z)) (dead_2: (@list Z)) (j: Z) (retval: Z)  __default__List_Z (PreH1 : (retval = (( &( "writers" ) ) + (0 * sizeof(INT))))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (LockTimesThrough ins locks_2 j )) (PreH17 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) (PreH18 : (aligned_4 (( &( "writers" ) ) + (0 * sizeof(INT))) )) ,
  (UCharArray.full (( &( "writers" ) ) + (0 * sizeof(INT))) (sizeof(INT) * (k_pre + 1 ) ) (repeat_Z (0) ((sizeof(INT) * (k_pre + 1 ) ))) )
|--
  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ”
.

Definition solver_entail_wit_5_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (locks_2: (@list Z)) (dead_2: (@list Z)) (j: Z) (retval: Z)  __default__List_Z (PreH1 : (retval = (( &( "writers" ) ) + (0 * sizeof(INT))))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (LockTimesThrough ins locks_2 j )) (PreH17 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) (PreH18 : (aligned_4 (( &( "writers" ) ) + (0 * sizeof(INT))) )) ,
  (UCharArray.full (( &( "writers" ) ) + (0 * sizeof(INT))) (sizeof(INT) * (k_pre + 1 ) ) (repeat_Z (0) ((sizeof(INT) * (k_pre + 1 ) ))) )
|--
  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ”
.

Definition solver_entail_wit_5_split_goal_spatial := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (locks_2: (@list Z)) (dead_2: (@list Z)) (j: Z) (retval: Z)  __default__List_Z (PreH1 : (retval = (( &( "writers" ) ) + (0 * sizeof(INT))))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (LockTimesThrough ins locks_2 j )) (PreH17 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) (PreH18 : (aligned_4 (( &( "writers" ) ) + (0 * sizeof(INT))) )) ,
  (UCharArray.full (( &( "writers" ) ) + (0 * sizeof(INT))) (sizeof(INT) * (k_pre + 1 ) ) (repeat_Z (0) ((sizeof(INT) * (k_pre + 1 ) ))) )
|--
  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) (repeat_Z (0) ((k_pre + 1 ))) )
.

Definition solver_entail_wit_6 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (locks_2: (@list Z)) (dead_2: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH13 : (0 <= j)) (PreH14 : (j < m_pre)) (PreH15 : (LockTimesThrough ins locks_2 j )) (PreH16 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks_2 )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead_2 )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) (repeat_Z (0) ((k_pre + 1 ))) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  EX (dead: (@list Z))  (locks: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (k_pre + 1 )) ” 
  &&  “ (LockTimesThrough ins locks j ) ” 
  &&  “ (DeadCellsThrough ins locks k_pre j dead ) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) (repeat_Z (0) ((k_pre + 1 ))) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 1 (repeat_Z ((-1)) ((1 - 1 ))) )
  **  (IntArray.undef_seg ( &( "first" ) ) 1 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (locks_2: (@list Z)) (dead_2: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH13 : (0 <= j)) (PreH14 : (j < m_pre)) (PreH15 : (LockTimesThrough ins locks_2 j )) (PreH16 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) ,
  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ ((repeat_Z ((-1)) ((1 - 1 ))) = (@nil Z)) ”
  &&  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.undef_seg ( &( "first" ) ) 1 105 )
).

Definition solver_entail_wit_6_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (locks_2: (@list Z)) (dead_2: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH13 : (0 <= j)) (PreH14 : (j < m_pre)) (PreH15 : (LockTimesThrough ins locks_2 j )) (PreH16 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) ,
  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ”
.

Definition solver_entail_wit_6_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (locks_2: (@list Z)) (dead_2: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH13 : (0 <= j)) (PreH14 : (j < m_pre)) (PreH15 : (LockTimesThrough ins locks_2 j )) (PreH16 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) ,
  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ”
.

Definition solver_entail_wit_6_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (locks_2: (@list Z)) (dead_2: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH13 : (0 <= j)) (PreH14 : (j < m_pre)) (PreH15 : (LockTimesThrough ins locks_2 j )) (PreH16 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) ,
  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ”
.

Definition solver_entail_wit_6_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (locks_2: (@list Z)) (dead_2: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH13 : (0 <= j)) (PreH14 : (j < m_pre)) (PreH15 : (LockTimesThrough ins locks_2 j )) (PreH16 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) ,
  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  “ ((repeat_Z ((-1)) ((1 - 1 ))) = (@nil Z)) ”
.

Definition solver_entail_wit_6_split_goal_spatial := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (locks_2: (@list Z)) (dead_2: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH13 : (0 <= j)) (PreH14 : (j < m_pre)) (PreH15 : (LockTimesThrough ins locks_2 j )) (PreH16 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) ,
  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.undef_seg ( &( "first" ) ) 1 105 )
.

Definition solver_entail_wit_7 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c <= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (LockTimesThrough ins locks_2 j )) (PreH19 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) ,
  (IntArray.seg ( &( "first" ) ) 1 (c + 1 ) (app ((repeat_Z ((-1)) ((c - 1 )))) ((cons ((-1)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "first" ) ) (c + 1 ) 105 )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks_2 )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead_2 )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) (repeat_Z (0) ((k_pre + 1 ))) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
|--
  EX (dead: (@list Z))  (locks: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (1 <= (c + 1 )) ” 
  &&  “ ((c + 1 ) <= (k_pre + 1 )) ” 
  &&  “ (LockTimesThrough ins locks j ) ” 
  &&  “ (DeadCellsThrough ins locks k_pre j dead ) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) (repeat_Z (0) ((k_pre + 1 ))) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (c + 1 ) (repeat_Z ((-1)) (((c + 1 ) - 1 ))) )
  **  (IntArray.undef_seg ( &( "first" ) ) (c + 1 ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c <= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (LockTimesThrough ins locks_2 j )) (PreH19 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) ,
  TT && emp 
|--
  “ ((app ((repeat_Z ((-1)) ((c - 1 )))) ((cons ((-1)) ((@nil Z))))) = (repeat_Z ((-1)) (((c + 1 ) - 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c <= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (LockTimesThrough ins locks_2 j )) (PreH19 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) ,
  ((app ((repeat_Z ((-1)) ((c - 1 )))) ((cons ((-1)) ((@nil Z))))) = (repeat_Z ((-1)) (((c + 1 ) - 1 ))))
.

Definition solver_entail_wit_8 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c > k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (LockTimesThrough ins locks_2 j )) (PreH19 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks_2 )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead_2 )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) (repeat_Z (0) ((k_pre + 1 ))) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 c (repeat_Z ((-1)) ((c - 1 ))) )
  **  (IntArray.undef_seg ( &( "first" ) ) c 105 )
|--
  EX (firsts: (@list Z))  (counts: (@list Z))  (locks: (@list Z))  (dead: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (DeadCellsBefore ins locks k_pre (j + 1 ) dead ) ” 
  &&  “ (DirectLockScan ins locks (j + 1 ) 0 ) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) 0 k_pre counts ) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c > k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (LockTimesThrough ins locks_2 j )) (PreH19 : (DeadCellsThrough ins locks_2 k_pre j dead_2 )) ,
  (IntArray.seg ( &( "first" ) ) 1 c (repeat_Z ((-1)) ((c - 1 ))) )
|--
  EX (firsts: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 ) ” 
  &&  “ (DirectLockScan ins locks_2 (j + 1 ) 0 ) ” 
  &&  “ (WriterCounts ins locks_2 (j + 1 ) 0 k_pre (repeat_Z (0) ((k_pre + 1 ))) ) ”
  &&  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
).

Definition solver_entail_wit_9 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH2 : ((Znth i locks 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (0 <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH21 : (DirectLockScan ins locks (j + 1 ) i )) (PreH22 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0))) ” 
  &&  “ ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre) ” 
  &&  “ ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0) ” 
  &&  “ ((Znth i locks 0) = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (DeadCellsBefore ins locks k_pre (j + 1 ) dead ) ” 
  &&  “ (DirectLockScan ins locks (j + 1 ) i ) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) i k_pre counts ) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH2 : ((Znth i locks 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (0 <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH21 : (DirectLockScan ins locks (j + 1 ) i )) (PreH22 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) ,
  TT && emp 
|--
  “ ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre) ” 
  &&  “ (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0))) ”
  &&  emp
).

Definition solver_entail_wit_9_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH2 : ((Znth i locks 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (0 <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH21 : (DirectLockScan ins locks (j + 1 ) i )) (PreH22 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) ,
  ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)
.

Definition solver_entail_wit_9_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH2 : ((Znth i locks 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (0 <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH21 : (DirectLockScan ins locks (j + 1 ) i )) (PreH22 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) ,
  (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))
.

Definition solver_entail_wit_10_1 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts_2: (@list Z)) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 1 ) firsts_2 0) < 0)) (PreH2 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH4 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH5 : ((Znth i locks_2 0) = 0)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (Pre k_pre ins )) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH15 : (n_pre = (Zlength (ins)))) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH17 : ((Zlength (xrows)) = n_pre)) (PreH18 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH19 : (0 <= j)) (PreH20 : (j < m_pre)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH24 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH25 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) (PreH26 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead_2 0) = 0)) ,
  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) (replace_Znth (((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 1 )) (i) (firsts_2)) )
  **  (IntArray.full ( &( "writers" ) ) (k_pre + 1 ) (replace_Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0))) (((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 0 ) counts_2 0) + 1 )) (counts_2)) )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead_2 )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks_2 )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  EX (firsts: (@list Z))  (counts: (@list Z))  (locks: (@list Z))  (dead: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (DeadCellsBefore ins locks k_pre (j + 1 ) dead ) ” 
  &&  “ (DirectLockScan ins locks (j + 1 ) (i + 1 ) ) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) (i + 1 ) k_pre counts ) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts_2: (@list Z)) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 1 ) firsts_2 0) < 0)) (PreH2 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH4 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH5 : ((Znth i locks_2 0) = 0)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (Pre k_pre ins )) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH15 : (n_pre = (Zlength (ins)))) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH17 : ((Zlength (xrows)) = n_pre)) (PreH18 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH19 : (0 <= j)) (PreH20 : (j < m_pre)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH24 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH25 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) (PreH26 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead_2 0) = 0)) ,
  (IntArray.full ( &( "writers" ) ) (k_pre + 1 ) (replace_Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0))) (((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 0 ) counts_2 0) + 1 )) (counts_2)) )
|--
  EX (counts: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 ) ” 
  &&  “ (DirectLockScan ins locks_2 (j + 1 ) (i + 1 ) ) ” 
  &&  “ (WriterCounts ins locks_2 (j + 1 ) (i + 1 ) k_pre counts ) ”
  &&  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
).

Definition solver_entail_wit_10_2 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts_2: (@list Z)) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 1 ) firsts_2 0) >= 0)) (PreH2 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH4 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH5 : ((Znth i locks_2 0) = 0)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (Pre k_pre ins )) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH15 : (n_pre = (Zlength (ins)))) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH17 : ((Zlength (xrows)) = n_pre)) (PreH18 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH19 : (0 <= j)) (PreH20 : (j < m_pre)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH24 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH25 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) (PreH26 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead_2 0) = 0)) ,
  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts_2 )
  **  (IntArray.full ( &( "writers" ) ) (k_pre + 1 ) (replace_Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0))) (((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 0 ) counts_2 0) + 1 )) (counts_2)) )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead_2 )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks_2 )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  EX (firsts: (@list Z))  (counts: (@list Z))  (locks: (@list Z))  (dead: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (DeadCellsBefore ins locks k_pre (j + 1 ) dead ) ” 
  &&  “ (DirectLockScan ins locks (j + 1 ) (i + 1 ) ) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) (i + 1 ) k_pre counts ) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts_2: (@list Z)) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 1 ) firsts_2 0) >= 0)) (PreH2 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH4 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH5 : ((Znth i locks_2 0) = 0)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (Pre k_pre ins )) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH15 : (n_pre = (Zlength (ins)))) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH17 : ((Zlength (xrows)) = n_pre)) (PreH18 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH19 : (0 <= j)) (PreH20 : (j < m_pre)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH24 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH25 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) (PreH26 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead_2 0) = 0)) ,
  (IntArray.full ( &( "writers" ) ) (k_pre + 1 ) (replace_Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0))) (((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 0 ) counts_2 0) + 1 )) (counts_2)) )
|--
  EX (counts: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 ) ” 
  &&  “ (DirectLockScan ins locks_2 (j + 1 ) (i + 1 ) ) ” 
  &&  “ (WriterCounts ins locks_2 (j + 1 ) (i + 1 ) k_pre counts ) ”
  &&  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
).

Definition solver_entail_wit_10_3 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts_2: (@list Z)) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth i locks_2 0) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH20 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH21 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) ,
  (IntArray.full lock_pre n_pre locks_2 )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead_2 )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts_2 )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts_2 )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  EX (firsts: (@list Z))  (counts: (@list Z))  (locks: (@list Z))  (dead: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (DeadCellsBefore ins locks k_pre (j + 1 ) dead ) ” 
  &&  “ (DirectLockScan ins locks (j + 1 ) (i + 1 ) ) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) (i + 1 ) k_pre counts ) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth i locks_2 0) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH20 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH21 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) ,
  TT && emp 
|--
  “ (WriterCounts ins locks_2 (j + 1 ) (i + 1 ) k_pre counts_2 ) ” 
  &&  “ (DirectLockScan ins locks_2 (j + 1 ) (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_10_3_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth i locks_2 0) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH20 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH21 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) ,
  (WriterCounts ins locks_2 (j + 1 ) (i + 1 ) k_pre counts_2 )
.

Definition solver_entail_wit_10_3_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth i locks_2 0) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH20 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH21 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) ,
  (DirectLockScan ins locks_2 (j + 1 ) (i + 1 ) )
.

Definition solver_entail_wit_10_4 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts_2: (@list Z)) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) = 0)) (PreH2 : ((Znth i locks_2 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (0 <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH21 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH22 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks_2 )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead_2 )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts_2 )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts_2 )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  EX (firsts: (@list Z))  (counts: (@list Z))  (locks: (@list Z))  (dead: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (DeadCellsBefore ins locks k_pre (j + 1 ) dead ) ” 
  &&  “ (DirectLockScan ins locks (j + 1 ) (i + 1 ) ) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) (i + 1 ) k_pre counts ) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) = 0)) (PreH2 : ((Znth i locks_2 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (0 <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH21 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH22 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) ,
  TT && emp 
|--
  “ (WriterCounts ins locks_2 (j + 1 ) (i + 1 ) k_pre counts_2 ) ” 
  &&  “ (DirectLockScan ins locks_2 (j + 1 ) (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_10_4_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) = 0)) (PreH2 : ((Znth i locks_2 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (0 <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH21 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH22 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) ,
  (WriterCounts ins locks_2 (j + 1 ) (i + 1 ) k_pre counts_2 )
.

Definition solver_entail_wit_10_4_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) = 0)) (PreH2 : ((Znth i locks_2 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (0 <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH21 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH22 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) ,
  (DirectLockScan ins locks_2 (j + 1 ) (i + 1 ) )
.

Definition solver_entail_wit_10_5 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts_2: (@list Z)) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH4 : ((Znth i locks_2 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (Pre k_pre ins )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH14 : (n_pre = (Zlength (ins)))) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH16 : ((Zlength (xrows)) = n_pre)) (PreH17 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH18 : (0 <= j)) (PreH19 : (j < m_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH23 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH24 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) (PreH25 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead_2 0) <> 0)) ,
  (IntArray.full lock_pre n_pre (replace_Znth (i) ((j + 1 )) (locks_2)) )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead_2 )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts_2 )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts_2 )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  EX (firsts: (@list Z))  (counts: (@list Z))  (locks: (@list Z))  (dead: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (DeadCellsBefore ins locks k_pre (j + 1 ) dead ) ” 
  &&  “ (DirectLockScan ins locks (j + 1 ) (i + 1 ) ) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) (i + 1 ) k_pre counts ) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH4 : ((Znth i locks_2 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (Pre k_pre ins )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH14 : (n_pre = (Zlength (ins)))) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH16 : ((Zlength (xrows)) = n_pre)) (PreH17 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH18 : (0 <= j)) (PreH19 : (j < m_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH23 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH24 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) (PreH25 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead_2 0) <> 0)) ,
  TT && emp 
|--
  “ (WriterCounts ins (replace_Znth (i) ((j + 1 )) (locks_2)) (j + 1 ) (i + 1 ) k_pre counts_2 ) ” 
  &&  “ (DirectLockScan ins (replace_Znth (i) ((j + 1 )) (locks_2)) (j + 1 ) (i + 1 ) ) ” 
  &&  “ (DeadCellsBefore ins (replace_Znth (i) ((j + 1 )) (locks_2)) k_pre (j + 1 ) dead_2 ) ”
  &&  emp
).

Definition solver_entail_wit_10_5_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH4 : ((Znth i locks_2 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (Pre k_pre ins )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH14 : (n_pre = (Zlength (ins)))) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH16 : ((Zlength (xrows)) = n_pre)) (PreH17 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH18 : (0 <= j)) (PreH19 : (j < m_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH23 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH24 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) (PreH25 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead_2 0) <> 0)) ,
  (WriterCounts ins (replace_Znth (i) ((j + 1 )) (locks_2)) (j + 1 ) (i + 1 ) k_pre counts_2 )
.

Definition solver_entail_wit_10_5_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH4 : ((Znth i locks_2 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (Pre k_pre ins )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH14 : (n_pre = (Zlength (ins)))) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH16 : ((Zlength (xrows)) = n_pre)) (PreH17 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH18 : (0 <= j)) (PreH19 : (j < m_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH23 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH24 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) (PreH25 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead_2 0) <> 0)) ,
  (DirectLockScan ins (replace_Znth (i) ((j + 1 )) (locks_2)) (j + 1 ) (i + 1 ) )
.

Definition solver_entail_wit_10_5_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH4 : ((Znth i locks_2 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (Pre k_pre ins )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH14 : (n_pre = (Zlength (ins)))) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH16 : ((Zlength (xrows)) = n_pre)) (PreH17 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH18 : (0 <= j)) (PreH19 : (j < m_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH23 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH24 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) (PreH25 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead_2 0) <> 0)) ,
  (DeadCellsBefore ins (replace_Znth (i) ((j + 1 )) (locks_2)) k_pre (j + 1 ) dead_2 )
.

Definition solver_entail_wit_11 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts_2: (@list Z)) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH19 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH20 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks_2 )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead_2 )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts_2 )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts_2 )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  EX (firsts: (@list Z))  (dead: (@list Z))  (locks: (@list Z))  (counts: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (k_pre + 1 )) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) n_pre k_pre counts ) ” 
  &&  “ (CellMarksPrefix ins locks counts k_pre (j + 1 ) 1 dead ) ” 
  &&  “ (CollisionClosurePrefix ins locks counts (j + 1 ) 1 0 ) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH19 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH20 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) ,
  TT && emp 
|--
  “ (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) 1 0 ) ” 
  &&  “ (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) 1 dead_2 ) ” 
  &&  “ (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 ) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ”
  &&  emp
).

Definition solver_entail_wit_11_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH19 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH20 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) ,
  (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) 1 0 )
.

Definition solver_entail_wit_11_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH19 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH20 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) ,
  (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) 1 dead_2 )
.

Definition solver_entail_wit_11_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH19 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH20 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) ,
  (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )
.

Definition solver_entail_wit_11_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH19 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH20 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) ,
  forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))
.

Definition solver_entail_wit_11_split_goal_5 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH19 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH20 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) ,
  forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))
.

Definition solver_entail_wit_11_split_goal_6 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (counts_2: (@list Z)) (locks_2: (@list Z)) (dead_2: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (DeadCellsBefore ins locks_2 k_pre (j + 1 ) dead_2 )) (PreH19 : (DirectLockScan ins locks_2 (j + 1 ) i )) (PreH20 : (WriterCounts ins locks_2 (j + 1 ) i k_pre counts_2 )) ,
  forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))
.

Definition solver_entail_wit_12 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts_2: (@list Z)) (dead_2: (@list Z)) (locks_2: (@list Z)) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (c - 0 ) counts_2 0) >= 2)) (PreH2 : (c <= k_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (1 <= c)) (PreH18 : (c <= (k_pre + 1 ))) (PreH19 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH20 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) c dead_2 )) (PreH21 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c 0 )) ,
  (IntArray.full ( &( "cell_locked" ) ) 105 (replace_Znth (c) (1) (dead_2)) )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts_2 )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks_2 )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts_2 )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  EX (firsts: (@list Z))  (dead: (@list Z))  (locks: (@list Z))  (counts: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (1 <= c) ” 
  &&  “ (c <= k_pre) ” 
  &&  “ (2 <= (Znth c counts 0)) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) n_pre k_pre counts ) ” 
  &&  “ (CellMarksPrefix ins locks counts k_pre (j + 1 ) (c + 1 ) dead ) ” 
  &&  “ (CollisionClosurePrefix ins locks counts (j + 1 ) c 0 ) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (c - 0 ) counts_2 0) >= 2)) (PreH2 : (c <= k_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (1 <= c)) (PreH18 : (c <= (k_pre + 1 ))) (PreH19 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH20 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) c dead_2 )) (PreH21 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c 0 )) ,
  TT && emp 
|--
  “ (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) (replace_Znth (c) (1) (dead_2)) ) ” 
  &&  “ (2 <= (Znth c counts_2 0)) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ”
  &&  emp
).

Definition solver_entail_wit_12_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (c - 0 ) counts_2 0) >= 2)) (PreH2 : (c <= k_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (1 <= c)) (PreH18 : (c <= (k_pre + 1 ))) (PreH19 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH20 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) c dead_2 )) (PreH21 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c 0 )) ,
  (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) (replace_Znth (c) (1) (dead_2)) )
.

Definition solver_entail_wit_12_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (c - 0 ) counts_2 0) >= 2)) (PreH2 : (c <= k_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (1 <= c)) (PreH18 : (c <= (k_pre + 1 ))) (PreH19 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH20 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) c dead_2 )) (PreH21 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c 0 )) ,
  (2 <= (Znth c counts_2 0))
.

Definition solver_entail_wit_12_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (c - 0 ) counts_2 0) >= 2)) (PreH2 : (c <= k_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (1 <= c)) (PreH18 : (c <= (k_pre + 1 ))) (PreH19 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH20 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) c dead_2 )) (PreH21 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c 0 )) ,
  forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))
.

Definition solver_entail_wit_12_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (c - 0 ) counts_2 0) >= 2)) (PreH2 : (c <= k_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (1 <= c)) (PreH18 : (c <= (k_pre + 1 ))) (PreH19 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH20 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) c dead_2 )) (PreH21 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c 0 )) ,
  forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))
.

Definition solver_entail_wit_12_split_goal_5 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (c - 0 ) counts_2 0) >= 2)) (PreH2 : (c <= k_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (1 <= c)) (PreH18 : (c <= (k_pre + 1 ))) (PreH19 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH20 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) c dead_2 )) (PreH21 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c 0 )) ,
  forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))
.

Definition solver_entail_wit_13_1 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts_2: (@list Z)) (dead_2: (@list Z)) (locks_2: (@list Z)) (i: Z) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) = c)) (PreH2 : ((Znth i locks_2 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (1 <= c)) (PreH19 : (c <= k_pre)) (PreH20 : (2 <= (Znth c counts_2 0))) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH24 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 )) (PreH25 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c i )) ,
  (IntArray.full lock_pre n_pre (replace_Znth (i) ((j + 1 )) (locks_2)) )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead_2 )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts_2 )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts_2 )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  EX (firsts: (@list Z))  (dead: (@list Z))  (locks: (@list Z))  (counts: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (1 <= c) ” 
  &&  “ (c <= k_pre) ” 
  &&  “ (2 <= (Znth c counts 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) n_pre k_pre counts ) ” 
  &&  “ (CellMarksPrefix ins locks counts k_pre (j + 1 ) (c + 1 ) dead ) ” 
  &&  “ (CollisionClosurePrefix ins locks counts (j + 1 ) c (i + 1 ) ) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (i: Z) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) = c)) (PreH2 : ((Znth i locks_2 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (1 <= c)) (PreH19 : (c <= k_pre)) (PreH20 : (2 <= (Znth c counts_2 0))) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH24 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 )) (PreH25 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c i )) ,
  TT && emp 
|--
  “ (CollisionClosurePrefix ins (replace_Znth (i) ((j + 1 )) (locks_2)) counts_2 (j + 1 ) c (i + 1 ) ) ” 
  &&  “ (CellMarksPrefix ins (replace_Znth (i) ((j + 1 )) (locks_2)) counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 ) ” 
  &&  “ (WriterCounts ins (replace_Znth (i) ((j + 1 )) (locks_2)) (j + 1 ) n_pre k_pre counts_2 ) ”
  &&  emp
).

Definition solver_entail_wit_13_1_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (i: Z) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) = c)) (PreH2 : ((Znth i locks_2 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (1 <= c)) (PreH19 : (c <= k_pre)) (PreH20 : (2 <= (Znth c counts_2 0))) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH24 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 )) (PreH25 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c i )) ,
  (CollisionClosurePrefix ins (replace_Znth (i) ((j + 1 )) (locks_2)) counts_2 (j + 1 ) c (i + 1 ) )
.

Definition solver_entail_wit_13_1_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (i: Z) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) = c)) (PreH2 : ((Znth i locks_2 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (1 <= c)) (PreH19 : (c <= k_pre)) (PreH20 : (2 <= (Znth c counts_2 0))) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH24 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 )) (PreH25 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c i )) ,
  (CellMarksPrefix ins (replace_Znth (i) ((j + 1 )) (locks_2)) counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 )
.

Definition solver_entail_wit_13_1_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (i: Z) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) = c)) (PreH2 : ((Znth i locks_2 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (1 <= c)) (PreH19 : (c <= k_pre)) (PreH20 : (2 <= (Znth c counts_2 0))) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH24 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 )) (PreH25 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c i )) ,
  (WriterCounts ins (replace_Znth (i) ((j + 1 )) (locks_2)) (j + 1 ) n_pre k_pre counts_2 )
.

Definition solver_entail_wit_13_2 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts_2: (@list Z)) (dead_2: (@list Z)) (locks_2: (@list Z)) (i: Z) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth i locks_2 0) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (1 <= c)) (PreH18 : (c <= k_pre)) (PreH19 : (2 <= (Znth c counts_2 0))) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH23 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 )) (PreH24 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c i )) ,
  (IntArray.full lock_pre n_pre locks_2 )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead_2 )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts_2 )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts_2 )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  EX (firsts: (@list Z))  (dead: (@list Z))  (locks: (@list Z))  (counts: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (1 <= c) ” 
  &&  “ (c <= k_pre) ” 
  &&  “ (2 <= (Znth c counts 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) n_pre k_pre counts ) ” 
  &&  “ (CellMarksPrefix ins locks counts k_pre (j + 1 ) (c + 1 ) dead ) ” 
  &&  “ (CollisionClosurePrefix ins locks counts (j + 1 ) c (i + 1 ) ) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (i: Z) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth i locks_2 0) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (1 <= c)) (PreH18 : (c <= k_pre)) (PreH19 : (2 <= (Znth c counts_2 0))) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH23 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 )) (PreH24 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c i )) ,
  TT && emp 
|--
  “ (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_13_2_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (i: Z) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth i locks_2 0) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (1 <= c)) (PreH18 : (c <= k_pre)) (PreH19 : (2 <= (Znth c counts_2 0))) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH23 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 )) (PreH24 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c i )) ,
  (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c (i + 1 ) )
.

Definition solver_entail_wit_13_3 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts_2: (@list Z)) (dead_2: (@list Z)) (locks_2: (@list Z)) (i: Z) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> c)) (PreH2 : ((Znth i locks_2 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (1 <= c)) (PreH19 : (c <= k_pre)) (PreH20 : (2 <= (Znth c counts_2 0))) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH24 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 )) (PreH25 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c i )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks_2 )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead_2 )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts_2 )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts_2 )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  EX (firsts: (@list Z))  (dead: (@list Z))  (locks: (@list Z))  (counts: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (1 <= c) ” 
  &&  “ (c <= k_pre) ” 
  &&  “ (2 <= (Znth c counts 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) n_pre k_pre counts ) ” 
  &&  “ (CellMarksPrefix ins locks counts k_pre (j + 1 ) (c + 1 ) dead ) ” 
  &&  “ (CollisionClosurePrefix ins locks counts (j + 1 ) c (i + 1 ) ) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (i: Z) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> c)) (PreH2 : ((Znth i locks_2 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (1 <= c)) (PreH19 : (c <= k_pre)) (PreH20 : (2 <= (Znth c counts_2 0))) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH24 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 )) (PreH25 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c i )) ,
  TT && emp 
|--
  “ (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_13_3_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (i: Z) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> c)) (PreH2 : ((Znth i locks_2 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (1 <= c)) (PreH19 : (c <= k_pre)) (PreH20 : (2 <= (Znth c counts_2 0))) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH24 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 )) (PreH25 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c i )) ,
  (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c (i + 1 ) )
.

Definition solver_entail_wit_14 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead_2: (@list Z)) (locks_2: (@list Z)) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c > k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts )) (PreH19 : (CellMarksPrefix ins locks_2 counts k_pre (j + 1 ) c dead_2 )) (PreH20 : (CollisionClosurePrefix ins locks_2 counts (j + 1 ) c 0 )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks_2 )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead_2 )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  EX (dead: (@list Z))  (locks: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= m_pre) ” 
  &&  “ (LockTimesThrough ins locks (j + 1 ) ) ” 
  &&  “ (DeadCellsThrough ins locks k_pre (j + 1 ) dead ) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.undef_full ( &( "writers" ) ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead_2: (@list Z)) (locks_2: (@list Z)) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c > k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts )) (PreH19 : (CellMarksPrefix ins locks_2 counts k_pre (j + 1 ) c dead_2 )) (PreH20 : (CollisionClosurePrefix ins locks_2 counts (j + 1 ) c 0 )) ,
  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (DeadCellsThrough ins locks_2 k_pre (j + 1 ) dead_2 ) ” 
  &&  “ (LockTimesThrough ins locks_2 (j + 1 ) ) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ”
  &&  (IntArray.undef_full ( &( "writers" ) ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
).

Definition solver_entail_wit_14_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead_2: (@list Z)) (locks_2: (@list Z)) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c > k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts )) (PreH19 : (CellMarksPrefix ins locks_2 counts k_pre (j + 1 ) c dead_2 )) (PreH20 : (CollisionClosurePrefix ins locks_2 counts (j + 1 ) c 0 )) ,
  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (DeadCellsThrough ins locks_2 k_pre (j + 1 ) dead_2 ) ”
.

Definition solver_entail_wit_14_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead_2: (@list Z)) (locks_2: (@list Z)) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c > k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts )) (PreH19 : (CellMarksPrefix ins locks_2 counts k_pre (j + 1 ) c dead_2 )) (PreH20 : (CollisionClosurePrefix ins locks_2 counts (j + 1 ) c 0 )) ,
  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (LockTimesThrough ins locks_2 (j + 1 ) ) ”
.

Definition solver_entail_wit_14_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead_2: (@list Z)) (locks_2: (@list Z)) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c > k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts )) (PreH19 : (CellMarksPrefix ins locks_2 counts k_pre (j + 1 ) c dead_2 )) (PreH20 : (CollisionClosurePrefix ins locks_2 counts (j + 1 ) c 0 )) ,
  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ”
.

Definition solver_entail_wit_14_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead_2: (@list Z)) (locks_2: (@list Z)) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c > k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts )) (PreH19 : (CellMarksPrefix ins locks_2 counts k_pre (j + 1 ) c dead_2 )) (PreH20 : (CollisionClosurePrefix ins locks_2 counts (j + 1 ) c 0 )) ,
  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ”
.

Definition solver_entail_wit_14_split_goal_5 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead_2: (@list Z)) (locks_2: (@list Z)) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c > k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts )) (PreH19 : (CellMarksPrefix ins locks_2 counts k_pre (j + 1 ) c dead_2 )) (PreH20 : (CollisionClosurePrefix ins locks_2 counts (j + 1 ) c 0 )) ,
  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ”
.

Definition solver_entail_wit_14_split_goal_spatial := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead_2: (@list Z)) (locks_2: (@list Z)) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c > k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts )) (PreH19 : (CellMarksPrefix ins locks_2 counts k_pre (j + 1 ) c dead_2 )) (PreH20 : (CollisionClosurePrefix ins locks_2 counts (j + 1 ) c 0 )) ,
  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  (IntArray.undef_full ( &( "writers" ) ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
.

Definition solver_entail_wit_15_1 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts_2: (@list Z)) (dead_2: (@list Z)) (locks_2: (@list Z)) (i: Z) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= k_pre)) (PreH18 : (2 <= (Znth c counts_2 0))) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH22 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 )) (PreH23 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c i )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks_2 )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead_2 )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts_2 )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts_2 )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  EX (firsts: (@list Z))  (dead: (@list Z))  (locks: (@list Z))  (counts: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (1 <= (c + 1 )) ” 
  &&  “ ((c + 1 ) <= (k_pre + 1 )) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) n_pre k_pre counts ) ” 
  &&  “ (CellMarksPrefix ins locks counts k_pre (j + 1 ) (c + 1 ) dead ) ” 
  &&  “ (CollisionClosurePrefix ins locks counts (j + 1 ) (c + 1 ) 0 ) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (i: Z) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= k_pre)) (PreH18 : (2 <= (Znth c counts_2 0))) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH22 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 )) (PreH23 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c i )) ,
  TT && emp 
|--
  “ (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) (c + 1 ) 0 ) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ”
  &&  emp
).

Definition solver_entail_wit_15_1_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (i: Z) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= k_pre)) (PreH18 : (2 <= (Znth c counts_2 0))) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH22 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 )) (PreH23 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c i )) ,
  (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) (c + 1 ) 0 )
.

Definition solver_entail_wit_15_1_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (i: Z) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= k_pre)) (PreH18 : (2 <= (Znth c counts_2 0))) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH22 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 )) (PreH23 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c i )) ,
  forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))
.

Definition solver_entail_wit_15_1_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (i: Z) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= k_pre)) (PreH18 : (2 <= (Znth c counts_2 0))) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH22 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 )) (PreH23 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c i )) ,
  forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))
.

Definition solver_entail_wit_15_1_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (i: Z) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < (n_pre * m_pre ))) -> ((0 <= (Znth q_2 (concat (ins)) 0)) /\ ((Znth q_2 (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_4: Z) , (((0 <= r_4) /\ (r_4 < n_pre)) -> (((Zlength ((Znth r_4 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_4 xrows __default__List_Z))) = (Znth r_4 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= k_pre)) (PreH18 : (2 <= (Znth c counts_2 0))) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH22 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 )) (PreH23 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c i )) ,
  forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))
.

Definition solver_entail_wit_15_2 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts_2: (@list Z)) (dead_2: (@list Z)) (locks_2: (@list Z)) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (c - 0 ) counts_2 0) < 2)) (PreH2 : (c <= k_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (1 <= c)) (PreH18 : (c <= (k_pre + 1 ))) (PreH19 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH20 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) c dead_2 )) (PreH21 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c 0 )) ,
  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts_2 )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks_2 )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead_2 )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts_2 )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  EX (firsts: (@list Z))  (dead: (@list Z))  (locks: (@list Z))  (counts: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (1 <= (c + 1 )) ” 
  &&  “ ((c + 1 ) <= (k_pre + 1 )) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) n_pre k_pre counts ) ” 
  &&  “ (CellMarksPrefix ins locks counts k_pre (j + 1 ) (c + 1 ) dead ) ” 
  &&  “ (CollisionClosurePrefix ins locks counts (j + 1 ) (c + 1 ) 0 ) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (c - 0 ) counts_2 0) < 2)) (PreH2 : (c <= k_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (1 <= c)) (PreH18 : (c <= (k_pre + 1 ))) (PreH19 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH20 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) c dead_2 )) (PreH21 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c 0 )) ,
  TT && emp 
|--
  “ (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) (c + 1 ) 0 ) ” 
  &&  “ (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 ) ”
  &&  emp
).

Definition solver_entail_wit_15_2_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (c - 0 ) counts_2 0) < 2)) (PreH2 : (c <= k_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (1 <= c)) (PreH18 : (c <= (k_pre + 1 ))) (PreH19 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH20 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) c dead_2 )) (PreH21 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c 0 )) ,
  (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) (c + 1 ) 0 )
.

Definition solver_entail_wit_15_2_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead_2: (@list Z)) (locks_2: (@list Z)) (counts_2: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (c - 0 ) counts_2 0) < 2)) (PreH2 : (c <= k_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (1 <= c)) (PreH18 : (c <= (k_pre + 1 ))) (PreH19 : (WriterCounts ins locks_2 (j + 1 ) n_pre k_pre counts_2 )) (PreH20 : (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) c dead_2 )) (PreH21 : (CollisionClosurePrefix ins locks_2 counts_2 (j + 1 ) c 0 )) ,
  (CellMarksPrefix ins locks_2 counts_2 k_pre (j + 1 ) (c + 1 ) dead_2 )
.

Definition solver_return_wit_1 := 
(
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead: (@list Z)) (locks: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (j >= m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j <= m_pre)) (PreH16 : (LockTimesThrough ins locks j )) (PreH17 : (DeadCellsThrough ins locks k_pre j dead )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
|--
  EX (out: (@list Z)) ,
  “ (Spec k_pre ins out ) ” 
  &&  “ ((Zlength (out)) = n_pre) ”
  &&  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre out )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead: (@list Z)) (locks: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (j >= m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j <= m_pre)) (PreH16 : (LockTimesThrough ins locks j )) (PreH17 : (DeadCellsThrough ins locks k_pre j dead )) ,
  TT && emp 
|--
  “ ((Zlength (locks)) = n_pre) ” 
  &&  “ (Spec k_pre ins locks ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead: (@list Z)) (locks: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (j >= m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j <= m_pre)) (PreH16 : (LockTimesThrough ins locks j )) (PreH17 : (DeadCellsThrough ins locks k_pre j dead )) ,
  ((Zlength (locks)) = n_pre)
.

Definition solver_return_wit_1_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead: (@list Z)) (locks: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (j >= m_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j <= m_pre)) (PreH16 : (LockTimesThrough ins locks j )) (PreH17 : (DeadCellsThrough ins locks k_pre j dead )) ,
  (Spec k_pre ins locks )
.

Definition solver_partial_solve_wit_1 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.seg lock_pre 0 i (repeat_Z (0) (i)) )
  **  (IntArray.undef_seg lock_pre i n_pre )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 (repeat_Z (0) (105)) )
  **  (IntArray.undef_full ( &( "writers" ) ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((lock_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg lock_pre (i + 1 ) n_pre )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.seg lock_pre 0 i (repeat_Z (0) (i)) )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 (repeat_Z (0) (105)) )
  **  (IntArray.undef_full ( &( "writers" ) ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
.

Definition solver_partial_solve_wit_2_pure := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (locks: (@list Z)) (dead: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH13 : (0 <= j)) (PreH14 : (j < m_pre)) (PreH15 : (LockTimesThrough ins locks j )) (PreH16 : (DeadCellsThrough ins locks k_pre j dead )) (PreH17 : (aligned_4 (( &( "writers" ) ) + (0 * sizeof(INT))) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "lock" ) )) # Ptr  |-> lock_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (UCharArray.undef_full (( &( "writers" ) ) + (0 * sizeof(INT))) (sizeof(INT) * (k_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  “ (0 <= (sizeof(INT) * (k_pre + 1 ) )) ” 
  &&  “ (0 = 0) ”
.

Definition solver_partial_solve_wit_2_aux := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (locks: (@list Z)) (dead: (@list Z)) (j: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 100)) (PreH3 : (Pre k_pre ins )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH9 : (n_pre = (Zlength (ins)))) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH11 : ((Zlength (xrows)) = n_pre)) (PreH12 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH13 : (0 <= j)) (PreH14 : (j < m_pre)) (PreH15 : (LockTimesThrough ins locks j )) (PreH16 : (DeadCellsThrough ins locks k_pre j dead )) (PreH17 : (aligned_4 (( &( "writers" ) ) + (0 * sizeof(INT))) )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (UCharArray.undef_full (( &( "writers" ) ) + (0 * sizeof(INT))) (sizeof(INT) * (k_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
|--
  “ (0 <= (sizeof(INT) * (k_pre + 1 ) )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (LockTimesThrough ins locks j ) ” 
  &&  “ (DeadCellsThrough ins locks k_pre j dead ) ” 
  &&  “ (aligned_4 (( &( "writers" ) ) + (0 * sizeof(INT))) ) ”
  &&  (UCharArray.undef_full (( &( "writers" ) ) + (0 * sizeof(INT))) (sizeof(INT) * (k_pre + 1 ) ) )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_full ( &( "first" ) ) 105 )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (dead: (@list Z)) (locks: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c <= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (LockTimesThrough ins locks j )) (PreH19 : (DeadCellsThrough ins locks k_pre j dead )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) (repeat_Z (0) ((k_pre + 1 ))) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 c (repeat_Z ((-1)) ((c - 1 ))) )
  **  (IntArray.undef_seg ( &( "first" ) ) c 105 )
|--
  “ (c <= k_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (1 <= c) ” 
  &&  “ (c <= (k_pre + 1 )) ” 
  &&  “ (LockTimesThrough ins locks j ) ” 
  &&  “ (DeadCellsThrough ins locks k_pre j dead ) ”
  &&  (((( &( "first" ) ) + (c * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "first" ) ) (c + 1 ) 105 )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) (repeat_Z (0) ((k_pre + 1 ))) )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 c (repeat_Z ((-1)) ((c - 1 ))) )
.

Definition solver_partial_solve_wit_4 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH19 : (DirectLockScan ins locks (j + 1 ) i )) (PreH20 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (DeadCellsBefore ins locks k_pre (j + 1 ) dead ) ” 
  &&  “ (DirectLockScan ins locks (j + 1 ) i ) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) i k_pre counts ) ”
  &&  (((lock_pre + (i * sizeof(INT)))) # Int  |-> (Znth i locks 0))
  **  (IntArray.missing_i lock_pre i 0 n_pre locks )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
.

Definition solver_partial_solve_wit_5 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth i locks 0) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH20 : (DirectLockScan ins locks (j + 1 ) i )) (PreH21 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) ,
  (IntArray.full lock_pre n_pre locks )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ ((Znth i locks 0) = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (DeadCellsBefore ins locks k_pre (j + 1 ) dead ) ” 
  &&  “ (DirectLockScan ins locks (j + 1 ) i ) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) i k_pre counts ) ”
  &&  ((((x_pre + (i * (sizeof(INT) * 105))) + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i xrows __default__List_Z)) (0)))
  **  (IntArray.missing_i (x_pre + (i * (sizeof(INT) * 105))) j 0 105 (Znth i xrows __default__List_Z) )
  **  (IntArray2.missing_i x_pre i 0 n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
.

Definition solver_partial_solve_wit_6 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH2 : ((Znth i locks 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (0 <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH21 : (DirectLockScan ins locks (j + 1 ) i )) (PreH22 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0) ” 
  &&  “ ((Znth i locks 0) = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (DeadCellsBefore ins locks k_pre (j + 1 ) dead ) ” 
  &&  “ (DirectLockScan ins locks (j + 1 ) i ) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) i k_pre counts ) ”
  &&  ((((x_pre + (i * (sizeof(INT) * 105))) + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i xrows __default__List_Z)) (0)))
  **  (IntArray.missing_i (x_pre + (i * (sizeof(INT) * 105))) j 0 105 (Znth i xrows __default__List_Z) )
  **  (IntArray2.missing_i x_pre i 0 n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
.

Definition solver_partial_solve_wit_7 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH4 : ((Znth i locks 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (Pre k_pre ins )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH14 : (n_pre = (Zlength (ins)))) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH16 : ((Zlength (xrows)) = n_pre)) (PreH17 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH18 : (0 <= j)) (PreH19 : (j < m_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH23 : (DirectLockScan ins locks (j + 1 ) i )) (PreH24 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0))) ” 
  &&  “ ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre) ” 
  &&  “ ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0) ” 
  &&  “ ((Znth i locks 0) = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (DeadCellsBefore ins locks k_pre (j + 1 ) dead ) ” 
  &&  “ (DirectLockScan ins locks (j + 1 ) i ) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) i k_pre counts ) ”
  &&  (((( &( "cell_locked" ) ) + ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) * sizeof(INT)))) # Int  |-> (Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0))
  **  (IntArray.missing_i ( &( "cell_locked" ) ) (Znth (j) ((Znth i xrows __default__List_Z)) (0)) 0 105 dead )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
.

Definition solver_partial_solve_wit_8 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH4 : ((Znth i locks 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (Pre k_pre ins )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH14 : (n_pre = (Zlength (ins)))) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH16 : ((Zlength (xrows)) = n_pre)) (PreH17 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH18 : (0 <= j)) (PreH19 : (j < m_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH23 : (DirectLockScan ins locks (j + 1 ) i )) (PreH24 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) (PreH25 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) <> 0)) ,
  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0))) ” 
  &&  “ ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre) ” 
  &&  “ ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0) ” 
  &&  “ ((Znth i locks 0) = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (DeadCellsBefore ins locks k_pre (j + 1 ) dead ) ” 
  &&  “ (DirectLockScan ins locks (j + 1 ) i ) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) i k_pre counts ) ” 
  &&  “ ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) <> 0) ”
  &&  (((lock_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i lock_pre i 0 n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
.

Definition solver_partial_solve_wit_9 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH4 : ((Znth i locks 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (Pre k_pre ins )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH14 : (n_pre = (Zlength (ins)))) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH16 : ((Zlength (xrows)) = n_pre)) (PreH17 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH18 : (0 <= j)) (PreH19 : (j < m_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH23 : (DirectLockScan ins locks (j + 1 ) i )) (PreH24 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) (PreH25 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) = 0)) ,
  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0))) ” 
  &&  “ ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre) ” 
  &&  “ ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0) ” 
  &&  “ ((Znth i locks 0) = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (DeadCellsBefore ins locks k_pre (j + 1 ) dead ) ” 
  &&  “ (DirectLockScan ins locks (j + 1 ) i ) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) i k_pre counts ) ” 
  &&  “ ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) = 0) ”
  &&  (((( &( "writers" ) ) + ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) * sizeof(INT)))) # Int  |-> (Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 0 ) counts 0))
  **  (IntArray.missing_i ( &( "writers" ) ) (Znth (j) ((Znth i xrows __default__List_Z)) (0)) 0 (k_pre + 1 ) counts )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
.

Definition solver_partial_solve_wit_10 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH4 : ((Znth i locks 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (Pre k_pre ins )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH14 : (n_pre = (Zlength (ins)))) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH16 : ((Zlength (xrows)) = n_pre)) (PreH17 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH18 : (0 <= j)) (PreH19 : (j < m_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH23 : (DirectLockScan ins locks (j + 1 ) i )) (PreH24 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) (PreH25 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) = 0)) ,
  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0))) ” 
  &&  “ ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre) ” 
  &&  “ ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0) ” 
  &&  “ ((Znth i locks 0) = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (DeadCellsBefore ins locks k_pre (j + 1 ) dead ) ” 
  &&  “ (DirectLockScan ins locks (j + 1 ) i ) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) i k_pre counts ) ” 
  &&  “ ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) = 0) ”
  &&  (((( &( "writers" ) ) + ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "writers" ) ) (Znth (j) ((Znth i xrows __default__List_Z)) (0)) 0 (k_pre + 1 ) counts )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
.

Definition solver_partial_solve_wit_11 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH2 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH4 : ((Znth i locks 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 100)) (PreH8 : (Pre k_pre ins )) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 100)) (PreH13 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH14 : (n_pre = (Zlength (ins)))) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH16 : ((Zlength (xrows)) = n_pre)) (PreH17 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH18 : (0 <= j)) (PreH19 : (j < m_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH23 : (DirectLockScan ins locks (j + 1 ) i )) (PreH24 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) (PreH25 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) = 0)) ,
  (IntArray.full ( &( "writers" ) ) (k_pre + 1 ) (replace_Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0))) (((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 0 ) counts 0) + 1 )) (counts)) )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0))) ” 
  &&  “ ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre) ” 
  &&  “ ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0) ” 
  &&  “ ((Znth i locks 0) = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (DeadCellsBefore ins locks k_pre (j + 1 ) dead ) ” 
  &&  “ (DirectLockScan ins locks (j + 1 ) i ) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) i k_pre counts ) ” 
  &&  “ ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) = 0) ”
  &&  (((( &( "first" ) ) + ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) * sizeof(INT)))) # Int  |-> (Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 1 ) firsts 0))
  **  (IntArray.missing_i ( &( "first" ) ) (Znth (j) ((Znth i xrows __default__List_Z)) (0)) 1 (k_pre + 1 ) firsts )
  **  (IntArray.full ( &( "writers" ) ) (k_pre + 1 ) (replace_Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0))) (((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 0 ) counts 0) + 1 )) (counts)) )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
.

Definition solver_partial_solve_wit_12 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (counts: (@list Z)) (locks: (@list Z)) (dead: (@list Z)) (i: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 1 ) firsts 0) < 0)) (PreH2 : (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0)))) (PreH3 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre)) (PreH4 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0)) (PreH5 : ((Znth i locks 0) = 0)) (PreH6 : (i < n_pre)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 100)) (PreH9 : (Pre k_pre ins )) (PreH10 : (1 <= n_pre)) (PreH11 : (n_pre <= 100)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 100)) (PreH14 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH15 : (n_pre = (Zlength (ins)))) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH17 : ((Zlength (xrows)) = n_pre)) (PreH18 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH19 : (0 <= j)) (PreH20 : (j < m_pre)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (DeadCellsBefore ins locks k_pre (j + 1 ) dead )) (PreH24 : (DirectLockScan ins locks (j + 1 ) i )) (PreH25 : (WriterCounts ins locks (j + 1 ) i k_pre counts )) (PreH26 : ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) = 0)) ,
  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.full ( &( "writers" ) ) (k_pre + 1 ) (replace_Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0))) (((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 0 ) counts 0) + 1 )) (counts)) )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ ((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 1 ) firsts 0) < 0) ” 
  &&  “ (1 <= (Znth (j) ((Znth i xrows __default__List_Z)) (0))) ” 
  &&  “ ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <= k_pre) ” 
  &&  “ ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) <> 0) ” 
  &&  “ ((Znth i locks 0) = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (DeadCellsBefore ins locks k_pre (j + 1 ) dead ) ” 
  &&  “ (DirectLockScan ins locks (j + 1 ) i ) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) i k_pre counts ) ” 
  &&  “ ((Znth (Znth (j) ((Znth i xrows __default__List_Z)) (0)) dead 0) = 0) ”
  &&  (((( &( "first" ) ) + ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "first" ) ) (Znth (j) ((Znth i xrows __default__List_Z)) (0)) 1 (k_pre + 1 ) firsts )
  **  (IntArray.full ( &( "writers" ) ) (k_pre + 1 ) (replace_Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0))) (((Znth ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) - 0 ) counts 0) + 1 )) (counts)) )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
.

Definition solver_partial_solve_wit_13 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead: (@list Z)) (locks: (@list Z)) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (c <= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= (k_pre + 1 ))) (PreH18 : (WriterCounts ins locks (j + 1 ) n_pre k_pre counts )) (PreH19 : (CellMarksPrefix ins locks counts k_pre (j + 1 ) c dead )) (PreH20 : (CollisionClosurePrefix ins locks counts (j + 1 ) c 0 )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (c <= k_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (1 <= c) ” 
  &&  “ (c <= (k_pre + 1 )) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) n_pre k_pre counts ) ” 
  &&  “ (CellMarksPrefix ins locks counts k_pre (j + 1 ) c dead ) ” 
  &&  “ (CollisionClosurePrefix ins locks counts (j + 1 ) c 0 ) ”
  &&  (((( &( "writers" ) ) + (c * sizeof(INT)))) # Int  |-> (Znth (c - 0 ) counts 0))
  **  (IntArray.missing_i ( &( "writers" ) ) c 0 (k_pre + 1 ) counts )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
.

Definition solver_partial_solve_wit_14 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead: (@list Z)) (locks: (@list Z)) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (c - 0 ) counts 0) >= 2)) (PreH2 : (c <= k_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (1 <= c)) (PreH18 : (c <= (k_pre + 1 ))) (PreH19 : (WriterCounts ins locks (j + 1 ) n_pre k_pre counts )) (PreH20 : (CellMarksPrefix ins locks counts k_pre (j + 1 ) c dead )) (PreH21 : (CollisionClosurePrefix ins locks counts (j + 1 ) c 0 )) ,
  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ ((Znth (c - 0 ) counts 0) >= 2) ” 
  &&  “ (c <= k_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (1 <= c) ” 
  &&  “ (c <= (k_pre + 1 )) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) n_pre k_pre counts ) ” 
  &&  “ (CellMarksPrefix ins locks counts k_pre (j + 1 ) c dead ) ” 
  &&  “ (CollisionClosurePrefix ins locks counts (j + 1 ) c 0 ) ”
  &&  (((( &( "cell_locked" ) ) + (c * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "cell_locked" ) ) c 0 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
.

Definition solver_partial_solve_wit_15 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead: (@list Z)) (locks: (@list Z)) (i: Z) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 100)) (PreH4 : (Pre k_pre ins )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH10 : (n_pre = (Zlength (ins)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH12 : ((Zlength (xrows)) = n_pre)) (PreH13 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH14 : (0 <= j)) (PreH15 : (j < m_pre)) (PreH16 : (1 <= c)) (PreH17 : (c <= k_pre)) (PreH18 : (2 <= (Znth c counts 0))) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (WriterCounts ins locks (j + 1 ) n_pre k_pre counts )) (PreH22 : (CellMarksPrefix ins locks counts k_pre (j + 1 ) (c + 1 ) dead )) (PreH23 : (CollisionClosurePrefix ins locks counts (j + 1 ) c i )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (1 <= c) ” 
  &&  “ (c <= k_pre) ” 
  &&  “ (2 <= (Znth c counts 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) n_pre k_pre counts ) ” 
  &&  “ (CellMarksPrefix ins locks counts k_pre (j + 1 ) (c + 1 ) dead ) ” 
  &&  “ (CollisionClosurePrefix ins locks counts (j + 1 ) c i ) ”
  &&  (((lock_pre + (i * sizeof(INT)))) # Int  |-> (Znth i locks 0))
  **  (IntArray.missing_i lock_pre i 0 n_pre locks )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
.

Definition solver_partial_solve_wit_16 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead: (@list Z)) (locks: (@list Z)) (i: Z) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth i locks 0) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 100)) (PreH5 : (Pre k_pre ins )) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH11 : (n_pre = (Zlength (ins)))) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH13 : ((Zlength (xrows)) = n_pre)) (PreH14 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH15 : (0 <= j)) (PreH16 : (j < m_pre)) (PreH17 : (1 <= c)) (PreH18 : (c <= k_pre)) (PreH19 : (2 <= (Znth c counts 0))) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (WriterCounts ins locks (j + 1 ) n_pre k_pre counts )) (PreH23 : (CellMarksPrefix ins locks counts k_pre (j + 1 ) (c + 1 ) dead )) (PreH24 : (CollisionClosurePrefix ins locks counts (j + 1 ) c i )) ,
  (IntArray.full lock_pre n_pre locks )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ ((Znth i locks 0) = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (1 <= c) ” 
  &&  “ (c <= k_pre) ” 
  &&  “ (2 <= (Znth c counts 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) n_pre k_pre counts ) ” 
  &&  “ (CellMarksPrefix ins locks counts k_pre (j + 1 ) (c + 1 ) dead ) ” 
  &&  “ (CollisionClosurePrefix ins locks counts (j + 1 ) c i ) ”
  &&  ((((x_pre + (i * (sizeof(INT) * 105))) + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i xrows __default__List_Z)) (0)))
  **  (IntArray.missing_i (x_pre + (i * (sizeof(INT) * 105))) j 0 105 (Znth i xrows __default__List_Z) )
  **  (IntArray2.missing_i x_pre i 0 n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
.

Definition solver_partial_solve_wit_17 := 
forall (lock_pre: Z) (x_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (xrows: (@list (@list Z))) (ins: (@list (@list Z))) (firsts: (@list Z)) (dead: (@list Z)) (locks: (@list Z)) (i: Z) (counts: (@list Z)) (c: Z) (j: Z)  __default__List_Z (PreH1 : ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) = c)) (PreH2 : ((Znth i locks 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 100)) (PreH6 : (Pre k_pre ins )) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 100)) (PreH11 : forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre)))) (PreH12 : (n_pre = (Zlength (ins)))) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre))) (PreH14 : ((Zlength (xrows)) = n_pre)) (PreH15 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z))))) (PreH16 : (0 <= j)) (PreH17 : (j < m_pre)) (PreH18 : (1 <= c)) (PreH19 : (c <= k_pre)) (PreH20 : (2 <= (Znth c counts 0))) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (WriterCounts ins locks (j + 1 ) n_pre k_pre counts )) (PreH24 : (CellMarksPrefix ins locks counts k_pre (j + 1 ) (c + 1 ) dead )) (PreH25 : (CollisionClosurePrefix ins locks counts (j + 1 ) c i )) ,
  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full lock_pre n_pre locks )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
|--
  “ ((Znth (j) ((Znth i xrows __default__List_Z)) (0)) = c) ” 
  &&  “ ((Znth i locks 0) = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 100) ” 
  &&  “ (Pre k_pre ins ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < (n_pre * m_pre ))) -> ((0 <= (Znth q (concat (ins)) 0)) /\ ((Znth q (concat (ins)) 0) <= k_pre))) ” 
  &&  “ (n_pre = (Zlength (ins))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r ins __default__List_Z))) = m_pre)) ” 
  &&  “ ((Zlength (xrows)) = n_pre) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> (((Zlength ((Znth r_2 xrows __default__List_Z))) = 105) /\ ((sublist (0) (m_pre) ((Znth r_2 xrows __default__List_Z))) = (Znth r_2 ins __default__List_Z)))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (1 <= c) ” 
  &&  “ (c <= k_pre) ” 
  &&  “ (2 <= (Znth c counts 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (WriterCounts ins locks (j + 1 ) n_pre k_pre counts ) ” 
  &&  “ (CellMarksPrefix ins locks counts k_pre (j + 1 ) (c + 1 ) dead ) ” 
  &&  “ (CollisionClosurePrefix ins locks counts (j + 1 ) c i ) ”
  &&  (((lock_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i lock_pre i 0 n_pre locks )
  **  (IntArray2.full x_pre n_pre 105 xrows )
  **  (IntArray.full ( &( "cell_locked" ) ) 105 dead )
  **  (IntArray.seg ( &( "writers" ) ) 0 (k_pre + 1 ) counts )
  **  (IntArray.undef_seg ( &( "writers" ) ) (k_pre + 1 ) 105 )
  **  (IntArray.undef_seg ( &( "first" ) ) 0 1 )
  **  (IntArray.seg ( &( "first" ) ) 1 (k_pre + 1 ) firsts )
  **  (IntArray.undef_seg ( &( "first" ) ) (k_pre + 1 ) 105 )
.

Module Type VC_Correct.

Include array2_Strategy_Correct.
Include array2_char_Strategy_Correct.
Include int_array_Strategy_Correct.
Include char_array_Strategy_Correct.
Include array2_ext_Strategy_Correct.

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
Axiom proof_of_solver_safety_wit_31 : solver_safety_wit_31.
Axiom proof_of_solver_safety_wit_32 : solver_safety_wit_32.
Axiom proof_of_solver_safety_wit_33 : solver_safety_wit_33.
Axiom proof_of_solver_safety_wit_34 : solver_safety_wit_34.
Axiom proof_of_solver_safety_wit_35 : solver_safety_wit_35.
Axiom proof_of_solver_safety_wit_36 : solver_safety_wit_36.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Axiom proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Axiom proof_of_solver_entail_wit_10_3 : solver_entail_wit_10_3.
Axiom proof_of_solver_entail_wit_10_4 : solver_entail_wit_10_4.
Axiom proof_of_solver_entail_wit_10_5 : solver_entail_wit_10_5.
Axiom proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Axiom proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Axiom proof_of_solver_entail_wit_13_1 : solver_entail_wit_13_1.
Axiom proof_of_solver_entail_wit_13_2 : solver_entail_wit_13_2.
Axiom proof_of_solver_entail_wit_13_3 : solver_entail_wit_13_3.
Axiom proof_of_solver_entail_wit_14 : solver_entail_wit_14.
Axiom proof_of_solver_entail_wit_15_1 : solver_entail_wit_15_1.
Axiom proof_of_solver_entail_wit_15_2 : solver_entail_wit_15_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
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
Axiom proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16.
Axiom proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17.

End VC_Correct.
