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
From SimpleC.EE.LLM_bench.Algorithms.paint_house_ii Require Import paint_house_ii_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.paint_house_ii.paint_house_ii_lib.
Local Open Scope sac.
Require Import AUXLib.MonotonicList.
From MaxMinLib Require Import MaxMin Interface.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.

(* Proofs reused by the current witnesses, kept with their mathematical
   statements in this manual so they compile without a separate library. *)
Module ReusedProof.
Definition paint_house_ii_entail_wit_1 :=
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) ,
  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) < k_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1000000000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1000000000) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre 0 0 0 (-1) ) ”
  &&  (IntPtrArray2.full costs_pre n_pre costs_l ).

Definition paint_house_ii_entail_wit_2 :=
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (min2: Z) (min1: Z) (min1_color: Z) (i: Z)  __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-1) <= min1_color)) (PreH13 : (min1_color < k_pre)) (PreH14 : (0 <= min1)) (PreH15 : (min1 <= 1000000000)) (PreH16 : (0 <= min2)) (PreH17 : (min2 <= 1000000000)) (PreH18 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) ,
  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  EX (row_ptr: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((-1) <= min1_color) ” 
  &&  “ (min1_color < k_pre) ” 
  &&  “ (0 <= min1) ” 
  &&  “ (min1 <= 1000000000) ” 
  &&  “ (0 <= min2) ” 
  &&  “ (min2 <= 1000000000) ” 
  &&  “ (1000000000 = 1000000000) ” 
  &&  “ (1000000000 = 1000000000) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color ) ” 
  &&  “ (PaintHouseIIInnerState costs_l n_pre k_pre i 0 min1 min2 min1_color 1000000000 1000000000 (-1) ) ”
  &&  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) ).

Definition paint_house_ii_entail_wit_3 :=
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (row_ptr_2: Z) (i: Z) (min1_color: Z) (min1: Z) (min2: Z) (new_min1: Z) (new_min2: Z) (new_min1_color: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((-1) <= min1_color)) (PreH12 : (min1_color < k_pre)) (PreH13 : (0 <= min1)) (PreH14 : (min1 <= 1000000000)) (PreH15 : (0 <= min2)) (PreH16 : (min2 <= 1000000000)) (PreH17 : (new_min1 = 1000000000)) (PreH18 : (new_min2 = 1000000000)) (PreH19 : (new_min1_color = (-1))) (PreH20 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH21 : (PaintHouseIIInnerState costs_l n_pre k_pre i 0 min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr_2 costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_ptr_2 (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
|--
  EX (row_ptr: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ ((-1) <= min1_color) ” 
  &&  “ (min1_color < k_pre) ” 
  &&  “ (0 <= min1) ” 
  &&  “ (min1 <= 1000000000) ” 
  &&  “ (0 <= min2) ” 
  &&  “ (min2 <= 1000000000) ” 
  &&  “ ((-1) <= new_min1_color) ” 
  &&  “ (new_min1_color < k_pre) ” 
  &&  “ (0 <= new_min1) ” 
  &&  “ (new_min1 <= 1000000000) ” 
  &&  “ (0 <= new_min2) ” 
  &&  “ (new_min2 <= 1000000000) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color ) ” 
  &&  “ (PaintHouseIIInnerState costs_l n_pre k_pre i 0 min1 min2 min1_color new_min1 new_min2 new_min1_color ) ”
  &&  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) ).

Definition paint_house_ii_entail_wit_4_1 :=
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (row_ptr_2: Z) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c: Z) (i: Z)  __default__List_Z (PreH1 : (c = min1_color)) (PreH2 : (c < k_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= k_pre)) (PreH16 : ((-1) <= min1_color)) (PreH17 : (min1_color < k_pre)) (PreH18 : (0 <= min1)) (PreH19 : (min1 <= 1000000000)) (PreH20 : (0 <= min2)) (PreH21 : (min2 <= 1000000000)) (PreH22 : ((-1) <= new_min1_color)) (PreH23 : (new_min1_color < k_pre)) (PreH24 : (0 <= new_min1)) (PreH25 : (new_min1 <= 1000000000)) (PreH26 : (0 <= new_min2)) (PreH27 : (new_min2 <= 1000000000)) (PreH28 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH29 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr_2 costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_ptr_2 (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
|--
  EX (row_ptr: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= min2) ” 
  &&  “ (min2 <= 1000000000) ” 
  &&  “ (0 <= (Znth c (Znth i costs_l __default__List_Z) 0)) ” 
  &&  “ ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000) ” 
  &&  “ ((min2 + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000) ” 
  &&  “ (PaintHouseIIPrevSelection min1 min2 min1_color c min2 ) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color ) ” 
  &&  “ (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color ) ”
  &&  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) ).

Definition paint_house_ii_entail_wit_4_2 :=
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (row_ptr_2: Z) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c: Z) (i: Z)  __default__List_Z (PreH1 : (c <> min1_color)) (PreH2 : (c < k_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c <= k_pre)) (PreH16 : ((-1) <= min1_color)) (PreH17 : (min1_color < k_pre)) (PreH18 : (0 <= min1)) (PreH19 : (min1 <= 1000000000)) (PreH20 : (0 <= min2)) (PreH21 : (min2 <= 1000000000)) (PreH22 : ((-1) <= new_min1_color)) (PreH23 : (new_min1_color < k_pre)) (PreH24 : (0 <= new_min1)) (PreH25 : (new_min1 <= 1000000000)) (PreH26 : (0 <= new_min2)) (PreH27 : (new_min2 <= 1000000000)) (PreH28 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH29 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr_2 costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_ptr_2 (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
|--
  EX (row_ptr: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= min1) ” 
  &&  “ (min1 <= 1000000000) ” 
  &&  “ (0 <= (Znth c (Znth i costs_l __default__List_Z) 0)) ” 
  &&  “ ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000) ” 
  &&  “ ((min1 + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000) ” 
  &&  “ (PaintHouseIIPrevSelection min1 min2 min1_color c min1 ) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color ) ” 
  &&  “ (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color ) ”
  &&  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) ).

Definition paint_house_ii_entail_wit_5_1 :=
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) < new_min1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= c)) (PreH14 : (c < k_pre)) (PreH15 : (0 <= prev)) (PreH16 : (prev <= 1000000000)) (PreH17 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH18 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH19 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH20 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH21 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH22 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  EX (row_ptr: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= prev) ” 
  &&  “ (prev <= 1000000000) ” 
  &&  “ (0 <= (prev + (Znth c (Znth i costs_l __default__List_Z) 0) )) ” 
  &&  “ ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000) ” 
  &&  “ ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) = (prev + (Znth c (Znth i costs_l __default__List_Z) 0) )) ” 
  &&  “ (PaintHouseIIPrevSelection min1 min2 min1_color c prev ) ” 
  &&  “ ((-1) <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= (prev + (Znth c (Znth i costs_l __default__List_Z) 0) )) ” 
  &&  “ ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000) ” 
  &&  “ (0 <= new_min1) ” 
  &&  “ (new_min1 <= 1000000000) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color ) ” 
  &&  “ (PaintHouseIIInnerState costs_l n_pre k_pre i (c + 1 ) min1 min2 min1_color (prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) new_min1 c ) ”
  &&  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) ).

Definition paint_house_ii_entail_wit_5_2 :=
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) < new_min2)) (PreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= prev)) (PreH17 : (prev <= 1000000000)) (PreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  EX (row_ptr: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= prev) ” 
  &&  “ (prev <= 1000000000) ” 
  &&  “ (0 <= (prev + (Znth c (Znth i costs_l __default__List_Z) 0) )) ” 
  &&  “ ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000) ” 
  &&  “ ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) = (prev + (Znth c (Znth i costs_l __default__List_Z) 0) )) ” 
  &&  “ (PaintHouseIIPrevSelection min1 min2 min1_color c prev ) ” 
  &&  “ ((-1) <= new_min1_color) ” 
  &&  “ (new_min1_color < k_pre) ” 
  &&  “ (0 <= new_min1) ” 
  &&  “ (new_min1 <= 1000000000) ” 
  &&  “ (0 <= (prev + (Znth c (Znth i costs_l __default__List_Z) 0) )) ” 
  &&  “ ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color ) ” 
  &&  “ (PaintHouseIIInnerState costs_l n_pre k_pre i (c + 1 ) min1 min2 min1_color new_min1 (prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) new_min1_color ) ”
  &&  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) ).

Definition paint_house_ii_entail_wit_5_3 :=
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (c: Z) (prev: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min2)) (PreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 10000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 1000)) (PreH7 : ((n_pre * k_pre ) <= 1000000)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= c)) (PreH15 : (c < k_pre)) (PreH16 : (0 <= prev)) (PreH17 : (prev <= 1000000000)) (PreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) (PreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) (PreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) (PreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) (PreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  EX (row_ptr: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (col: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < k_pre) ” 
  &&  “ (0 <= prev) ” 
  &&  “ (prev <= 1000000000) ” 
  &&  “ (0 <= (prev + (Znth c (Znth i costs_l __default__List_Z) 0) )) ” 
  &&  “ ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000) ” 
  &&  “ ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) = (prev + (Znth c (Znth i costs_l __default__List_Z) 0) )) ” 
  &&  “ (PaintHouseIIPrevSelection min1 min2 min1_color c prev ) ” 
  &&  “ ((-1) <= new_min1_color) ” 
  &&  “ (new_min1_color < k_pre) ” 
  &&  “ (0 <= new_min1) ” 
  &&  “ (new_min1 <= 1000000000) ” 
  &&  “ (0 <= new_min2) ” 
  &&  “ (new_min2 <= 1000000000) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color ) ” 
  &&  “ (PaintHouseIIInnerState costs_l n_pre k_pre i (c + 1 ) min1 min2 min1_color new_min1 new_min2 new_min1_color ) ”
  &&  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) ).

Definition paint_house_ii_entail_wit_6 :=
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (row_ptr_2: Z) (i: Z) (c_2: Z) (prev: Z) (total: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min1: Z) (new_min2: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (col: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= c_2)) (PreH13 : (c_2 < k_pre)) (PreH14 : (0 <= prev)) (PreH15 : (prev <= 1000000000)) (PreH16 : (0 <= total)) (PreH17 : (total <= 1000000000)) (PreH18 : (total = (prev + (Znth c_2 (Znth i costs_l __default__List_Z) 0) ))) (PreH19 : (PaintHouseIIPrevSelection min1 min2 min1_color c_2 prev )) (PreH20 : ((-1) <= new_min1_color)) (PreH21 : (new_min1_color < k_pre)) (PreH22 : (0 <= new_min1)) (PreH23 : (new_min1 <= 1000000000)) (PreH24 : (0 <= new_min2)) (PreH25 : (new_min2 <= 1000000000)) (PreH26 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH27 : (PaintHouseIIInnerState costs_l n_pre k_pre i (c_2 + 1 ) min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr_2 costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_ptr_2 (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
|--
  EX (row_ptr: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (c_2 + 1 )) ” 
  &&  “ ((c_2 + 1 ) <= k_pre) ” 
  &&  “ ((-1) <= min1_color) ” 
  &&  “ (min1_color < k_pre) ” 
  &&  “ (0 <= min1) ” 
  &&  “ (min1 <= 1000000000) ” 
  &&  “ (0 <= min2) ” 
  &&  “ (min2 <= 1000000000) ” 
  &&  “ ((-1) <= new_min1_color) ” 
  &&  “ (new_min1_color < k_pre) ” 
  &&  “ (0 <= new_min1) ” 
  &&  “ (new_min1 <= 1000000000) ” 
  &&  “ (0 <= new_min2) ” 
  &&  “ (new_min2 <= 1000000000) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color ) ” 
  &&  “ (PaintHouseIIInnerState costs_l n_pre k_pre i (c_2 + 1 ) min1 min2 min1_color new_min1 new_min2 new_min1_color ) ”
  &&  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) ).

Definition paint_house_ii_entail_wit_7 :=
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (row_ptr: Z) (new_min2: Z) (new_min1: Z) (new_min1_color: Z) (min2: Z) (min1: Z) (min1_color: Z) (c_3: Z) (i: Z)  __default__List_Z (PreH1 : (c_3 >= k_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= c_3)) (PreH14 : (c_3 <= k_pre)) (PreH15 : ((-1) <= min1_color)) (PreH16 : (min1_color < k_pre)) (PreH17 : (0 <= min1)) (PreH18 : (min1 <= 1000000000)) (PreH19 : (0 <= min2)) (PreH20 : (min2 <= 1000000000)) (PreH21 : ((-1) <= new_min1_color)) (PreH22 : (new_min1_color < k_pre)) (PreH23 : (0 <= new_min1)) (PreH24 : (new_min1 <= 1000000000)) (PreH25 : (0 <= new_min2)) (PreH26 : (new_min2 <= 1000000000)) (PreH27 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH28 : (PaintHouseIIInnerState costs_l n_pre k_pre i c_3 min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.missing_i costs_pre n_pre i row_ptr costs_l )
  **  (((costs_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth i costs_l __default__List_Z))) (Znth i costs_l __default__List_Z) )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color ) ” 
  &&  “ (PaintHouseIIInnerState costs_l n_pre k_pre i k_pre min1 min2 min1_color new_min1 new_min2 new_min1_color ) ” 
  &&  “ (PaintHouseIICompletedRowState costs_l n_pre k_pre i min1 min2 min1_color new_min1 new_min2 new_min1_color ) ”
  &&  (IntPtrArray2.full costs_pre n_pre costs_l ).

Definition paint_house_ii_entail_wit_8 :=
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (i: Z) (min1_color: Z) (min2: Z) (min1: Z) (new_min1_color: Z) (new_min2: Z) (new_min1: Z)  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 10000)) (PreH3 : (2 <= k_pre)) (PreH4 : (k_pre <= 1000)) (PreH5 : ((n_pre * k_pre ) <= 1000000)) (PreH6 : ((Zlength (costs_l)) = n_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) (PreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) (PreH12 : (PaintHouseIIInnerState costs_l n_pre k_pre i k_pre min1 min2 min1_color new_min1 new_min2 new_min1_color )) (PreH13 : (PaintHouseIICompletedRowState costs_l n_pre k_pre i min1 min2 min1_color new_min1 new_min2 new_min1_color )) ,
  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 10000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 1000) ” 
  &&  “ ((n_pre * k_pre ) <= 1000000) ” 
  &&  “ ((Zlength (costs_l)) = n_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (new_min1 = new_min1) ” 
  &&  “ (new_min2 = new_min2) ” 
  &&  “ (new_min1_color = new_min1_color) ” 
  &&  “ (0 <= new_min1) ” 
  &&  “ (new_min1 <= 1000000000) ” 
  &&  “ (0 <= new_min2) ” 
  &&  “ (new_min2 <= 1000000000) ” 
  &&  “ (0 <= new_min1_color) ” 
  &&  “ (new_min1_color < k_pre) ” 
  &&  “ (PaintHouseIIDPState costs_l n_pre k_pre (i + 1 ) new_min1 new_min2 new_min1_color ) ”
  &&  (IntPtrArray2.full costs_pre n_pre costs_l ).

Definition paint_house_ii_return_wit_1 :=
forall (k_pre: Z) (n_pre: Z) (costs_pre: Z) (costs_l: (@list (@list Z))) (min2: Z) (min1: Z) (min1_color: Z) (i: Z)  __default__List_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000)) (PreH4 : (2 <= k_pre)) (PreH5 : (k_pre <= 1000)) (PreH6 : ((n_pre * k_pre ) <= 1000000)) (PreH7 : ((Zlength (costs_l)) = n_pre)) (PreH8 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l __default__List_Z))) = k_pre))) (PreH9 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l __default__List_Z) 0)) /\ ((Znth c (Znth r_2 costs_l __default__List_Z) 0) <= 10000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((-1) <= min1_color)) (PreH13 : (min1_color < k_pre)) (PreH14 : (0 <= min1)) (PreH15 : (min1 <= 1000000000)) (PreH16 : (0 <= min2)) (PreH17 : (min2 <= 1000000000)) (PreH18 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) ,
  (IntPtrArray2.full costs_pre n_pre costs_l )
|--
  “ (PaintHouseIIAnswer costs_l n_pre k_pre min1 ) ” 
  &&  “ (0 <= min1) ” 
  &&  “ (min1 <= 1000000000) ”
  &&  (IntPtrArray2.full costs_pre n_pre costs_l ).

Lemma proof_of_paint_house_ii_entail_wit_1 : paint_house_ii_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  entailer!.
  unfold PaintHouseIIDPState; auto.
Qed.
Lemma proof_of_paint_house_ii_entail_wit_2 : paint_house_ii_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    costs_pre i n_pre costs_l).
  - dump_pre_spatial; lia.
  - Intros row_ptr.
    Exists row_ptr.
    unfold StorePtrAsElement.storeA.
    entailer!.
    all: unfold PaintHouseIIInnerState, PaintHouseIIInf.
    all: repeat split; auto; try lia.
    all: rewrite sizeof_ptr.
    all: rewrite (Znth_indep costs_l i nil __default__List_Z) by lia.
    all: change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i costs_l __default__List_Z))
      (Znth i costs_l __default__List_Z)) with
      (IntArray.full row_ptr
        (Zlength (Znth i costs_l __default__List_Z))
        (Znth i costs_l __default__List_Z)).
    all: fold_arch.
    all: cancel.
Qed.
Lemma proof_of_paint_house_ii_entail_wit_3 : paint_house_ii_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists row_ptr_2.
  entailer!.
Qed.
Lemma proof_of_paint_house_ii_entail_wit_4_1 : paint_house_ii_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists row_ptr_2.
  entailer!.
  - unfold PaintHouseIIPrevSelection.
    subst c. destruct (Z.eq_dec min1_color min1_color);
      [reflexivity | contradiction].
  - assert (Hcost_bound: forall r col,
        0 <= r < n_pre ->
        0 <= col < k_pre ->
        0 <= PaintCostAt costs_l r col <= 10000).
    { intros r col Hr Hcol. unfold PaintCostAt.
      rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
      apply PreH10; repeat split; lia. }
    pose proof (PaintHouseIIDPState_values_bound__loop_core
                  costs_l n_pre k_pre i min1 min2 min1_color
                  PreH4 Hcost_bound PreH28) as [_ Hmin2_bound].
    pose proof (PreH10 i c) as Hcurrent_cost.
    specialize (Hcurrent_cost ltac:(intuition lia)).
    lia.
  - pose proof (PreH10 i c) as Hcurrent_cost.
    specialize (Hcurrent_cost ltac:(intuition lia)). lia.
  - pose proof (PreH10 i c) as Hcurrent_cost.
    specialize (Hcurrent_cost ltac:(intuition lia)). lia.
Qed.
Lemma proof_of_paint_house_ii_entail_wit_4_2 : paint_house_ii_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists row_ptr_2.
  entailer!.
  - unfold PaintHouseIIPrevSelection.
    destruct (Z.eq_dec c min1_color); [contradiction | reflexivity].
  - assert (Hcost_bound: forall r col,
        0 <= r < n_pre ->
        0 <= col < k_pre ->
        0 <= PaintCostAt costs_l r col <= 10000).
    { intros r col Hr Hcol. unfold PaintCostAt.
      rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
      apply PreH10; repeat split; lia. }
    pose proof (PaintHouseIIDPState_values_bound__loop_core
                  costs_l n_pre k_pre i min1 min2 min1_color
                  PreH4 Hcost_bound PreH28) as [Hmin1_bound _].
    pose proof (PreH10 i c) as Hcurrent_cost.
    specialize (Hcurrent_cost ltac:(intuition lia)).
    lia.
  - pose proof (PreH10 i c) as Hcurrent_cost.
    specialize (Hcurrent_cost ltac:(intuition lia)). lia.
  - pose proof (PreH10 i c) as Hcurrent_cost.
    specialize (Hcurrent_cost ltac:(intuition lia)). lia.
Qed.
Lemma proof_of_paint_house_ii_entail_wit_5_1 : paint_house_ii_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    costs_pre i n_pre costs_l).
  - dump_pre_spatial; lia.
  - Intros row_ptr.
    Exists row_ptr.
    unfold StorePtrAsElement.storeA.
    entailer!.
    + rewrite sizeof_ptr.
      rewrite (Znth_indep costs_l i nil __default__List_Z) by lia.
      change (IntPtrArray2.ElemArray.full row_ptr
        (Zlength (Znth i costs_l __default__List_Z))
        (Znth i costs_l __default__List_Z)) with
        (IntArray.full row_ptr
          (Zlength (Znth i costs_l __default__List_Z))
          (Znth i costs_l __default__List_Z)).
      fold_arch. cancel.
    + eapply PaintHouseIIInnerState_update_best__loop_core
        with (prev := prev);
        [ lia
        | exact PreH1
        | exact PreH20
        | unfold PaintCostAt;
          rewrite (Znth_indep costs_l i nil __default__List_Z) by lia;
          reflexivity
        | exact PreH22 ].
    + assert (Hcost_bound: forall r col,
        0 <= r < n_pre ->
        0 <= col < k_pre ->
        0 <= PaintCostAt costs_l r col <= 10000).
    { intros r col Hr Hcol. unfold PaintCostAt.
      rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
      apply PreH9; repeat split; lia. }
    pose proof (PaintHouseIIInnerState_values_bound__loop_core
                  costs_l n_pre k_pre i c min1 min2 min1_color
                  new_min1 new_min2 new_min1_color
                  PreH3 Hcost_bound PreH22)
      as [Hnew1_bound _].
    lia.
Qed.
Lemma proof_of_paint_house_ii_entail_wit_5_2 : paint_house_ii_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hcost_bound: forall r col,
      0 <= r < n_pre ->
      0 <= col < k_pre ->
      0 <= PaintCostAt costs_l r col <= 10000).
  { intros r col Hr Hcol. unfold PaintCostAt.
    rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
    apply PreH10; repeat split; lia. }
  pose proof (PaintHouseIIInnerState_values_bound__loop_core
                costs_l n_pre k_pre i c min1 min2 min1_color
                new_min1 new_min2 new_min1_color
                PreH4 Hcost_bound PreH23)
    as [Hnew1_bound [_ Hnew_color_bound]].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    costs_pre i n_pre costs_l).
  - dump_pre_spatial; lia.
  - Intros row_ptr.
    Exists row_ptr.
    unfold StorePtrAsElement.storeA.
    entailer!.
    + rewrite sizeof_ptr.
      rewrite (Znth_indep costs_l i nil __default__List_Z) by lia.
      change (IntPtrArray2.ElemArray.full row_ptr
        (Zlength (Znth i costs_l __default__List_Z))
        (Znth i costs_l __default__List_Z)) with
        (IntArray.full row_ptr
          (Zlength (Znth i costs_l __default__List_Z))
          (Znth i costs_l __default__List_Z)).
      fold_arch. cancel.
    + eapply PaintHouseIIInnerState_update_second__loop_core
        with (prev := prev);
        [ lia
        | apply Z.ge_le; exact PreH2
        | exact PreH1
        | exact PreH21
        | unfold PaintCostAt;
          rewrite (Znth_indep costs_l i nil __default__List_Z) by lia;
          reflexivity
        | exact PreH23 ].
Qed.
Lemma proof_of_paint_house_ii_entail_wit_5_3 : paint_house_ii_entail_wit_5_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hcost_bound: forall r col,
          0 <= r < n_pre ->
          0 <= col < k_pre ->
          0 <= PaintCostAt costs_l r col <= 10000).
  { intros r col Hr Hcol. unfold PaintCostAt.
    rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
    apply PreH10; repeat split; lia. }
  pose proof (PaintHouseIIInnerState_values_bound__loop_core
                costs_l n_pre k_pre i c min1 min2 min1_color
                new_min1 new_min2 new_min1_color
                PreH4 Hcost_bound PreH23)
    as [Hnew1_bound [Hnew2_bound Hnew_color_bound]].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    costs_pre i n_pre costs_l).
  - dump_pre_spatial; lia.
  - Intros row_ptr.
    Exists row_ptr.
    unfold StorePtrAsElement.storeA.
    entailer!.
    + rewrite sizeof_ptr.
      rewrite (Znth_indep costs_l i nil __default__List_Z) by lia.
      change (IntPtrArray2.ElemArray.full row_ptr
        (Zlength (Znth i costs_l __default__List_Z))
        (Znth i costs_l __default__List_Z)) with
        (IntArray.full row_ptr
          (Zlength (Znth i costs_l __default__List_Z))
          (Znth i costs_l __default__List_Z)).
      fold_arch. cancel.
    + eapply PaintHouseIIInnerState_keep__loop_core
        with (prev := prev) (total := prev + PaintCostAt costs_l i c).
      * lia.
      * replace (PaintCostAt costs_l i c)
          with (Znth c (Znth i costs_l __default__List_Z) 0).
        -- apply Z.ge_le. exact PreH2.
        -- unfold PaintCostAt.
           rewrite (Znth_indep costs_l i nil __default__List_Z) by lia.
           reflexivity.
      * replace (PaintCostAt costs_l i c)
          with (Znth c (Znth i costs_l __default__List_Z) 0).
        -- apply Z.ge_le. exact PreH1.
        -- unfold PaintCostAt.
           rewrite (Znth_indep costs_l i nil __default__List_Z) by lia.
           reflexivity.
      * pose proof (PaintHouseIIDPState_values_bound__loop_core
                      costs_l n_pre k_pre i min1 min2 min1_color
                      PreH4 Hcost_bound PreH22)
          as [Hmin1_bound Hmin2_bound].
        assert (Hi_cost_bound : i * 10000 <= 99990000) by lia.
        assert (Hpaint_cost_bound : PaintCostAt costs_l i c <= 10000).
        { unfold PaintCostAt.
          rewrite (Znth_indep costs_l i nil __default__List_Z) by lia.
          lia. }
        unfold PaintHouseIIPrevSelection in PreH21.
        destruct (Z.eq_dec c min1_color); subst prev;
          unfold PaintHouseIIInf; nia.
      * exact PreH21.
      * unfold PaintCostAt.
        rewrite (Znth_indep costs_l i nil __default__List_Z) by lia.
        reflexivity.
      * exact PreH23.
Qed.
Lemma proof_of_paint_house_ii_entail_wit_6 : paint_house_ii_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hcost_bound: forall r col,
      0 <= r < n_pre ->
      0 <= col < k_pre ->
      0 <= PaintCostAt costs_l r col <= 10000).
  { intros r col Hr Hcol. unfold PaintCostAt.
    rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
    apply PreH8; repeat split; lia. }
  pose proof (PaintHouseIIDPState_values_bound__loop_core
                costs_l n_pre k_pre i min1 min2 min1_color
                PreH2 Hcost_bound PreH26)
    as [Hmin1_bound Hmin2_bound].
  assert (Hcolor_bound: -1 <= min1_color < k_pre).
  { pose proof PreH26 as Hdp_shape.
    unfold PaintHouseIIDPState in Hdp_shape.
    destruct Hdp_shape as [[_ [_ [_ Hcolor]]] | [_ [Hcolor _]]];
      subst; lia. }
  Exists row_ptr_2.
  entailer!.
Qed.
Lemma proof_of_paint_house_ii_entail_wit_7 : paint_house_ii_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  entailer!.
  - pose proof (IntPtrArray2.missing_i_merge_to_full
      costs_pre i n_pre row_ptr costs_l
      (Znth i costs_l __default__List_Z)) as Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    rewrite sizeof_ptr.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i costs_l __default__List_Z))
      (Znth i costs_l __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth i costs_l __default__List_Z))
        (Znth i costs_l __default__List_Z)) in Hmerge.
    rewrite replace_Znth_Znth in Hmerge by lia.
    eapply derivable1_trans.
    + apply derivable1_sepcon_comm.
    + apply Hmerge; lia.
  - assert (c_3 = k_pre) by lia.
    subst c_3.
    eapply PaintHouseIIInnerState_completed_row__loop_core; eauto; lia.
  - assert (c_3 = k_pre) by lia.
    subst c_3.
    exact PreH28.
Qed.
Lemma proof_of_paint_house_ii_entail_wit_8 : paint_house_ii_entail_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hcost_bound: forall r col,
      0 <= r < n_pre ->
      0 <= col < k_pre ->
      0 <= PaintCostAt costs_l r col <= 10000).
  { intros r col Hr Hcol. unfold PaintCostAt.
    rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
    apply PreH8; repeat split; lia. }
  pose proof (PaintHouseIIInnerState_values_bound__loop_core
                costs_l n_pre k_pre i k_pre min1 min2 min1_color
                new_min1 new_min2 new_min1_color
                PreH2 Hcost_bound PreH12)
    as [Hnew1_bound [Hnew2_bound _]].
  pose proof (proj2 PreH13) as Hdp_next.
  assert (Hnew_color_bound: 0 <= new_min1_color < k_pre).
  { pose proof Hdp_next as Hdp_shape.
    unfold PaintHouseIIDPState in Hdp_shape.
    destruct Hdp_shape as [[Hrow _] | [_ [Hcolor _]]]; lia. }
  entailer!.
Qed.
Lemma proof_of_paint_house_ii_return_wit_1 : paint_house_ii_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      assert (i = n_pre) by lia.
      subst i.
      eapply PaintHouseIIDPState_answer__answer; eauto; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
Qed.
End ReusedProof.

Lemma paint_coloring_iff : forall k n colors,
  PaintHouseIIValidColoring k n colors <-> PaintHouseIILegalColoring k n colors.
Proof.
  intros k n colors. unfold PaintHouseIIValidColoring, PaintHouseIILegalColoring.
  rewrite (Forall_Znth (fun color => 0 <= color < k) (-1) colors).
  split; intros [Hlen [Hcolors Hadj]];
    (split; [exact Hlen | split; [intros i Hi; apply Hcolors; lia | exact Hadj]]).
Qed.
Lemma paint_answer_iff : forall costs n k answer,
  PaintHouseIIAnswer costs n k answer <-> PaintHouseIIOptimalCost costs n k answer.
Proof.
  intros costs n k answer.
  unfold PaintHouseIIAnswer, PaintHouseIIOptimalCost, min_value_of_subset, min_object_of_subset.
  split; intros [colors [[Hvalid Hleast] Hvalue]];
    (exists colors; split; [split | exact Hvalue]).
  - apply paint_coloring_iff. exact Hvalid.
  - intros xs Hxs. apply Hleast. apply paint_coloring_iff. exact Hxs.
  - apply paint_coloring_iff. exact Hvalid.
  - intros xs Hxs. apply Hleast. apply paint_coloring_iff. exact Hxs.
Qed.
Lemma paint_second_iff : forall costs n k row color value,
  row <= n ->
  (PaintHouseIISecondBestForColor costs n k row color value <->
   PaintHouseIIAlternativeMinimum costs n k row color value).
Proof.
  intros. unfold PaintHouseIISecondBestForColor, PaintHouseIIAlternativeMinimum.
  intuition lia.
Qed.
Lemma paint_dp_iff : forall costs n k row min1 min2 color,
  row <= n ->
  (PaintHouseIIDPState costs n k row min1 min2 color <->
   PaintHouseIIRowMinima costs n k row min1 min2 color).
Proof.
  intros costs n k row min1 min2 color Hrow.
  unfold PaintHouseIIDPState, PaintHouseIIRowMinima.
  rewrite paint_second_iff by lia. split.
  - intros [Hz | [Hr [Hcolor [Hbest Hsecond]]]].
    + left. exact Hz.
    + right. split; [lia | split; assumption].
  - intros [Hz | [Hr [Hbest Hsecond]]].
    + left. exact Hz.
    + right.
      pose proof (PaintHouseIIPrefixCost_color_bound__loop_core
        costs n k row color min1 Hr (proj1 Hbest)) as Hcolor.
      split; [lia | split; [exact Hcolor | split; assumption]].
Qed.
Lemma paint_inner_iff : forall costs n k row processed old1 old2 old_color new1 new2 new_color,
  0 <= row < n -> 0 <= processed <= k ->
  (PaintHouseIIInnerState costs n k row processed old1 old2 old_color new1 new2 new_color <->
   PaintHouseIIColorMinima costs n k row processed old1 old2 old_color new1 new2 new_color).
Proof.
  intros. unfold PaintHouseIIInnerState, PaintHouseIIColorMinima.
  rewrite paint_dp_iff by lia. intuition lia.
Qed.
Lemma paint_completed_iff : forall costs n k row old1 old2 old_color new1 new2 new_color,
  0 <= row < n -> 0 <= k ->
  (PaintHouseIICompletedRowState costs n k row old1 old2 old_color new1 new2 new_color <->
   PaintHouseIICompletedMinima costs n k row old1 old2 old_color new1 new2 new_color).
Proof.
  intros. unfold PaintHouseIICompletedRowState, PaintHouseIICompletedMinima.
  rewrite paint_inner_iff by lia. rewrite paint_dp_iff by lia. tauto.
Qed.
Lemma paint_rows_iff : forall (costs : list (list Z)) n k (d : list Z),
  Zlength costs = n ->
  (Forall (eq k) (map (@Zlength Z) costs) <->
   forall r, 0 <= r < n -> Zlength (Znth r costs d) = k).
Proof.
  intros costs n k d Hlen. rewrite Forall_map.
  rewrite (Forall_Znth (fun row => k = Zlength row) d costs).
  split; intros H r Hr; specialize (H r ltac:(lia)); lia.
Qed.
Lemma paint_costs_iff : forall (costs : list (list Z)) n k (d : list Z),
  Zlength costs = n -> Forall (eq k) (map (@Zlength Z) costs) ->
  ((Forall (Forall (Z.le 0)) costs /\ Forall (Forall (Z.ge 10000)) costs) <->
   forall r c, 0 <= r < n -> 0 <= c < k ->
     0 <= Znth c (Znth r costs d) 0 <= 10000).
Proof.
  intros costs n k d Hlen Hshape.
  pose proof ((proj1 (paint_rows_iff costs n k d Hlen)) Hshape) as Hrows.
  split.
  - intros [Hlo Hhi] r c Hr Hc.
    pose proof (proj1 (Forall_Znth (Forall (Z.le 0)) d costs) Hlo r ltac:(lia)) as Hlo_row.
    pose proof (proj1 (Forall_Znth (Forall (Z.ge 10000)) d costs) Hhi r ltac:(lia)) as Hhi_row.
    pose proof (Hrows r Hr) as Hrowlen.
    pose proof (proj1 (Forall_Znth (Z.le 0) 0 (Znth r costs d)) Hlo_row c ltac:(lia)) as Hl.
    pose proof (proj1 (Forall_Znth (Z.ge 10000) 0 (Znth r costs d)) Hhi_row c ltac:(lia)) as Hh.
    apply Z.ge_le in Hh. lia.
  - intros Hbounds. split.
    + apply (proj2 (Forall_Znth (Forall (Z.le 0)) d costs)). intros r Hr.
      apply (proj2 (Forall_Znth (Z.le 0) 0 (Znth r costs d))). intros c Hc.
      pose proof (Hrows r ltac:(lia)) as Hrowlen.
      specialize (Hbounds r c ltac:(lia) ltac:(lia)). lia.
    + apply (proj2 (Forall_Znth (Forall (Z.ge 10000)) d costs)). intros r Hr.
      apply (proj2 (Forall_Znth (Z.ge 10000) 0 (Znth r costs d))). intros c Hc.
      pose proof (Hrows r ltac:(lia)) as Hrowlen.
      specialize (Hbounds r c ltac:(lia) ltac:(lia)). apply Z.le_ge. lia.
Qed.
Ltac paint_math :=
  try solve [assumption | reflexivity];
  repeat rewrite paint_completed_iff in * by lia;
  repeat rewrite paint_inner_iff in * by lia;
  repeat rewrite paint_dp_iff in * by lia;
  repeat rewrite paint_answer_iff in *;
  try solve [assumption | reflexivity | intuition lia];
  try solve [intros; eauto 3; intuition lia].
























Lemma proof_of_paint_house_ii_entail_wit_1 : paint_house_ii_entail_wit_1.
Proof.
  unfold paint_house_ii_entail_wit_1; try left; intros.
  pose proof ((proj1 (paint_rows_iff costs_l n_pre k_pre (@nil Z) ltac:(lia))) ltac:(assumption)) as LegacyRows.
  pose proof ((proj1 (paint_costs_iff costs_l n_pre k_pre (@nil Z) ltac:(lia) ltac:(assumption))) ltac:(split; assumption)) as LegacyCosts.
  assert (LegacyCostInput : forall r col, (((0 <= r /\ r < n_pre) /\ 0 <= col) /\ col < k_pre) ->
    0 <= Znth col (Znth r costs_l (@nil Z)) 0 <= 10000).
  { intros r col Hr. apply LegacyCosts; tauto. }
  assert (LegacyPreH1 : (1 <= n_pre)) by paint_math.
  assert (LegacyPreH2 : (n_pre <= 10000)) by paint_math.
  assert (LegacyPreH3 : (2 <= k_pre)) by paint_math.
  assert (LegacyPreH4 : (k_pre <= 1000)) by paint_math.
  assert (LegacyPreH5 : ((n_pre * k_pre ) <= 1000000)) by paint_math.
  assert (LegacyPreH6 : ((Zlength (costs_l)) = n_pre)) by paint_math.
  assert (LegacyPreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l (@nil Z)))) = k_pre))) by paint_math.
  assert (LegacyPreH8 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l (@nil Z)) 0)) /\ ((Znth c_2 (Znth r_4 costs_l (@nil Z)) 0) <= 10000)))) by paint_math.
  pose proof (ReusedProof.proof_of_paint_house_ii_entail_wit_1 k_pre n_pre costs_pre costs_l (@nil Z) LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8) as Hreused.
  eapply derivable1_trans; [exact Hreused |].
  Intros.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; paint_math.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_2 : paint_house_ii_entail_wit_2.
Proof.
  unfold paint_house_ii_entail_wit_2; try left; intros.
  pose proof ((proj1 (paint_rows_iff costs_l n_pre k_pre __default__List_Z ltac:(lia))) ltac:(assumption)) as LegacyRows.
  pose proof ((proj1 (paint_costs_iff costs_l n_pre k_pre __default__List_Z ltac:(lia) ltac:(assumption))) ltac:(split; assumption)) as LegacyCosts.
  assert (LegacyCostInput : forall r col, (((0 <= r /\ r < n_pre) /\ 0 <= col) /\ col < k_pre) ->
    0 <= Znth col (Znth r costs_l __default__List_Z) 0 <= 10000).
  { intros r col Hr. apply LegacyCosts; tauto. }
  assert (LegacyPreH1 : (i < n_pre)) by paint_math.
  assert (LegacyPreH2 : (1 <= n_pre)) by paint_math.
  assert (LegacyPreH3 : (n_pre <= 10000)) by paint_math.
  assert (LegacyPreH4 : (2 <= k_pre)) by paint_math.
  assert (LegacyPreH5 : (k_pre <= 1000)) by paint_math.
  assert (LegacyPreH6 : ((n_pre * k_pre ) <= 1000000)) by paint_math.
  assert (LegacyPreH7 : ((Zlength (costs_l)) = n_pre)) by paint_math.
  assert (LegacyPreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) by paint_math.
  assert (LegacyPreH9 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) by paint_math.
  assert (LegacyPreH10 : (0 <= i)) by paint_math.
  assert (LegacyPreH11 : (i <= n_pre)) by paint_math.
  assert (LegacyPreH12 : ((-1) <= min1_color)) by paint_math.
  assert (LegacyPreH13 : (min1_color < k_pre)) by paint_math.
  assert (LegacyPreH14 : (0 <= min1)) by paint_math.
  assert (LegacyPreH15 : (min1 <= 1000000000)) by paint_math.
  assert (LegacyPreH16 : (0 <= min2)) by paint_math.
  assert (LegacyPreH17 : (min2 <= 1000000000)) by paint_math.
  assert (LegacyPreH18 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) by paint_math.
  pose proof (ReusedProof.proof_of_paint_house_ii_entail_wit_2 k_pre n_pre costs_pre costs_l min2 min1 min1_color i __default__List_Z LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18) as Hreused.
  eapply derivable1_trans; [exact Hreused |].
  Intros row_ptr_reused.
  Exists row_ptr_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; paint_math.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_3_1 : paint_house_ii_entail_wit_3_1.
Proof.
  unfold paint_house_ii_entail_wit_3_1; try left; intros.
  pose proof ((proj1 (paint_rows_iff costs_l n_pre k_pre __default__List_Z ltac:(lia))) ltac:(assumption)) as LegacyRows.
  pose proof ((proj1 (paint_costs_iff costs_l n_pre k_pre __default__List_Z ltac:(lia) ltac:(assumption))) ltac:(split; assumption)) as LegacyCosts.
  assert (LegacyCostInput : forall r col, (((0 <= r /\ r < n_pre) /\ 0 <= col) /\ col < k_pre) ->
    0 <= Znth col (Znth r costs_l __default__List_Z) 0 <= 10000).
  { intros r col Hr. apply LegacyCosts; tauto. }
  assert (LegacyPreH1 : (c = min1_color)) by paint_math.
  assert (LegacyPreH2 : (c < k_pre)) by paint_math.
  assert (LegacyPreH3 : (1 <= n_pre)) by paint_math.
  assert (LegacyPreH4 : (n_pre <= 10000)) by paint_math.
  assert (LegacyPreH5 : (2 <= k_pre)) by paint_math.
  assert (LegacyPreH6 : (k_pre <= 1000)) by paint_math.
  assert (LegacyPreH7 : ((n_pre * k_pre ) <= 1000000)) by paint_math.
  assert (LegacyPreH8 : ((Zlength (costs_l)) = n_pre)) by paint_math.
  assert (LegacyPreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) by paint_math.
  assert (LegacyPreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) by paint_math.
  assert (LegacyPreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) by paint_math.
  assert (LegacyPreH12 : (0 <= i)) by paint_math.
  assert (LegacyPreH13 : (i < n_pre)) by paint_math.
  assert (LegacyPreH14 : (0 <= c)) by paint_math.
  assert (LegacyPreH15 : (c <= k_pre)) by paint_math.
  assert (LegacyPreH16 : ((-1) <= min1_color)) by paint_math.
  assert (LegacyPreH17 : (min1_color < k_pre)) by paint_math.
  assert (LegacyPreH18 : (0 <= min1)) by paint_math.
  assert (LegacyPreH19 : (min1 <= 1000000000)) by paint_math.
  assert (LegacyPreH20 : (0 <= min2)) by paint_math.
  assert (LegacyPreH21 : (min2 <= 1000000000)) by paint_math.
  assert (LegacyPreH22 : ((-1) <= new_min1_color)) by paint_math.
  assert (LegacyPreH23 : (new_min1_color < k_pre)) by paint_math.
  assert (LegacyPreH24 : (0 <= new_min1)) by paint_math.
  assert (LegacyPreH25 : (new_min1 <= 1000000000)) by paint_math.
  assert (LegacyPreH26 : (0 <= new_min2)) by paint_math.
  assert (LegacyPreH27 : (new_min2 <= 1000000000)) by paint_math.
  assert (LegacyPreH28 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) by paint_math.
  assert (LegacyPreH29 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) by paint_math.
  pose proof (ReusedProof.proof_of_paint_house_ii_entail_wit_4_1 k_pre n_pre costs_pre costs_l row_ptr_2 new_min2 new_min1 new_min1_color min2 min1 min1_color c i __default__List_Z LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20 LegacyPreH21 LegacyPreH22 LegacyPreH23 LegacyPreH24 LegacyPreH25 LegacyPreH26 LegacyPreH27 LegacyPreH28 LegacyPreH29) as Hreused.
  eapply derivable1_trans; [exact Hreused |].
  Intros row_ptr_reused.
  Exists row_ptr_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; paint_math.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_3_2 : paint_house_ii_entail_wit_3_2.
Proof.
  unfold paint_house_ii_entail_wit_3_2; try left; intros.
  pose proof ((proj1 (paint_rows_iff costs_l n_pre k_pre __default__List_Z ltac:(lia))) ltac:(assumption)) as LegacyRows.
  pose proof ((proj1 (paint_costs_iff costs_l n_pre k_pre __default__List_Z ltac:(lia) ltac:(assumption))) ltac:(split; assumption)) as LegacyCosts.
  assert (LegacyCostInput : forall r col, (((0 <= r /\ r < n_pre) /\ 0 <= col) /\ col < k_pre) ->
    0 <= Znth col (Znth r costs_l __default__List_Z) 0 <= 10000).
  { intros r col Hr. apply LegacyCosts; tauto. }
  assert (LegacyPreH1 : (c <> min1_color)) by paint_math.
  assert (LegacyPreH2 : (c < k_pre)) by paint_math.
  assert (LegacyPreH3 : (1 <= n_pre)) by paint_math.
  assert (LegacyPreH4 : (n_pre <= 10000)) by paint_math.
  assert (LegacyPreH5 : (2 <= k_pre)) by paint_math.
  assert (LegacyPreH6 : (k_pre <= 1000)) by paint_math.
  assert (LegacyPreH7 : ((n_pre * k_pre ) <= 1000000)) by paint_math.
  assert (LegacyPreH8 : ((Zlength (costs_l)) = n_pre)) by paint_math.
  assert (LegacyPreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) by paint_math.
  assert (LegacyPreH10 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= c_2)) /\ (c_2 < k_pre)) -> ((0 <= (Znth c_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) by paint_math.
  assert (LegacyPreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) by paint_math.
  assert (LegacyPreH12 : (0 <= i)) by paint_math.
  assert (LegacyPreH13 : (i < n_pre)) by paint_math.
  assert (LegacyPreH14 : (0 <= c)) by paint_math.
  assert (LegacyPreH15 : (c <= k_pre)) by paint_math.
  assert (LegacyPreH16 : ((-1) <= min1_color)) by paint_math.
  assert (LegacyPreH17 : (min1_color < k_pre)) by paint_math.
  assert (LegacyPreH18 : (0 <= min1)) by paint_math.
  assert (LegacyPreH19 : (min1 <= 1000000000)) by paint_math.
  assert (LegacyPreH20 : (0 <= min2)) by paint_math.
  assert (LegacyPreH21 : (min2 <= 1000000000)) by paint_math.
  assert (LegacyPreH22 : ((-1) <= new_min1_color)) by paint_math.
  assert (LegacyPreH23 : (new_min1_color < k_pre)) by paint_math.
  assert (LegacyPreH24 : (0 <= new_min1)) by paint_math.
  assert (LegacyPreH25 : (new_min1 <= 1000000000)) by paint_math.
  assert (LegacyPreH26 : (0 <= new_min2)) by paint_math.
  assert (LegacyPreH27 : (new_min2 <= 1000000000)) by paint_math.
  assert (LegacyPreH28 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) by paint_math.
  assert (LegacyPreH29 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) by paint_math.
  pose proof (ReusedProof.proof_of_paint_house_ii_entail_wit_4_2 k_pre n_pre costs_pre costs_l row_ptr_2 new_min2 new_min1 new_min1_color min2 min1 min1_color c i __default__List_Z LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20 LegacyPreH21 LegacyPreH22 LegacyPreH23 LegacyPreH24 LegacyPreH25 LegacyPreH26 LegacyPreH27 LegacyPreH28 LegacyPreH29) as Hreused.
  eapply derivable1_trans; [exact Hreused |].
  Intros row_ptr_reused.
  Exists row_ptr_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; paint_math.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_4_1 : paint_house_ii_entail_wit_4_1.
Proof.
  unfold paint_house_ii_entail_wit_4_1; try left; intros.
  pose proof ((proj1 (paint_rows_iff costs_l n_pre k_pre __default__List_Z ltac:(lia))) ltac:(assumption)) as LegacyRows.
  pose proof ((proj1 (paint_costs_iff costs_l n_pre k_pre __default__List_Z ltac:(lia) ltac:(assumption))) ltac:(split; assumption)) as LegacyCosts.
  assert (LegacyCostInput : forall r col, (((0 <= r /\ r < n_pre) /\ 0 <= col) /\ col < k_pre) ->
    0 <= Znth col (Znth r costs_l __default__List_Z) 0 <= 10000).
  { intros r col Hr. apply LegacyCosts; tauto. }
  assert (LegacyPreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) < new_min1)) by paint_math.
  assert (LegacyPreH2 : (1 <= n_pre)) by paint_math.
  assert (LegacyPreH3 : (n_pre <= 10000)) by paint_math.
  assert (LegacyPreH4 : (2 <= k_pre)) by paint_math.
  assert (LegacyPreH5 : (k_pre <= 1000)) by paint_math.
  assert (LegacyPreH6 : ((n_pre * k_pre ) <= 1000000)) by paint_math.
  assert (LegacyPreH7 : ((Zlength (costs_l)) = n_pre)) by paint_math.
  assert (LegacyPreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) by paint_math.
  assert (LegacyPreH9 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) by paint_math.
  assert (LegacyPreH10 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) by paint_math.
  assert (LegacyPreH11 : (0 <= i)) by paint_math.
  assert (LegacyPreH12 : (i < n_pre)) by paint_math.
  assert (LegacyPreH13 : (0 <= c)) by paint_math.
  assert (LegacyPreH14 : (c < k_pre)) by paint_math.
  assert (LegacyPreH15 : (0 <= prev)) by paint_math.
  assert (LegacyPreH16 : (prev <= 1000000000)) by paint_math.
  assert (LegacyPreH17 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) by paint_math.
  assert (LegacyPreH18 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) by paint_math.
  assert (LegacyPreH19 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) by paint_math.
  assert (LegacyPreH20 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) by paint_math.
  assert (LegacyPreH21 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) by paint_math.
  assert (LegacyPreH22 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) by paint_math.
  pose proof (ReusedProof.proof_of_paint_house_ii_entail_wit_5_1 k_pre n_pre costs_pre costs_l i c prev min1_color min2 min1 new_min1_color new_min2 new_min1 __default__List_Z LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20 LegacyPreH21 LegacyPreH22) as Hreused.
  eapply derivable1_trans; [exact Hreused |].
  Intros row_ptr_reused.
  Exists row_ptr_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; paint_math.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_4_2 : paint_house_ii_entail_wit_4_2.
Proof.
  unfold paint_house_ii_entail_wit_4_2; try left; intros.
  pose proof ((proj1 (paint_rows_iff costs_l n_pre k_pre __default__List_Z ltac:(lia))) ltac:(assumption)) as LegacyRows.
  pose proof ((proj1 (paint_costs_iff costs_l n_pre k_pre __default__List_Z ltac:(lia) ltac:(assumption))) ltac:(split; assumption)) as LegacyCosts.
  assert (LegacyCostInput : forall r col, (((0 <= r /\ r < n_pre) /\ 0 <= col) /\ col < k_pre) ->
    0 <= Znth col (Znth r costs_l __default__List_Z) 0 <= 10000).
  { intros r col Hr. apply LegacyCosts; tauto. }
  assert (LegacyPreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) < new_min2)) by paint_math.
  assert (LegacyPreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) by paint_math.
  assert (LegacyPreH3 : (1 <= n_pre)) by paint_math.
  assert (LegacyPreH4 : (n_pre <= 10000)) by paint_math.
  assert (LegacyPreH5 : (2 <= k_pre)) by paint_math.
  assert (LegacyPreH6 : (k_pre <= 1000)) by paint_math.
  assert (LegacyPreH7 : ((n_pre * k_pre ) <= 1000000)) by paint_math.
  assert (LegacyPreH8 : ((Zlength (costs_l)) = n_pre)) by paint_math.
  assert (LegacyPreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) by paint_math.
  assert (LegacyPreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) by paint_math.
  assert (LegacyPreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) by paint_math.
  assert (LegacyPreH12 : (0 <= i)) by paint_math.
  assert (LegacyPreH13 : (i < n_pre)) by paint_math.
  assert (LegacyPreH14 : (0 <= c)) by paint_math.
  assert (LegacyPreH15 : (c < k_pre)) by paint_math.
  assert (LegacyPreH16 : (0 <= prev)) by paint_math.
  assert (LegacyPreH17 : (prev <= 1000000000)) by paint_math.
  assert (LegacyPreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) by paint_math.
  assert (LegacyPreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) by paint_math.
  assert (LegacyPreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) by paint_math.
  assert (LegacyPreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) by paint_math.
  assert (LegacyPreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) by paint_math.
  assert (LegacyPreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) by paint_math.
  pose proof (ReusedProof.proof_of_paint_house_ii_entail_wit_5_2 k_pre n_pre costs_pre costs_l i c prev min1_color min2 min1 new_min1_color new_min2 new_min1 __default__List_Z LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20 LegacyPreH21 LegacyPreH22 LegacyPreH23) as Hreused.
  eapply derivable1_trans; [exact Hreused |].
  Intros row_ptr_reused.
  Exists row_ptr_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; paint_math.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_4_3 : paint_house_ii_entail_wit_4_3.
Proof.
  unfold paint_house_ii_entail_wit_4_3; try left; intros.
  pose proof ((proj1 (paint_rows_iff costs_l n_pre k_pre __default__List_Z ltac:(lia))) ltac:(assumption)) as LegacyRows.
  pose proof ((proj1 (paint_costs_iff costs_l n_pre k_pre __default__List_Z ltac:(lia) ltac:(assumption))) ltac:(split; assumption)) as LegacyCosts.
  assert (LegacyCostInput : forall r col, (((0 <= r /\ r < n_pre) /\ 0 <= col) /\ col < k_pre) ->
    0 <= Znth col (Znth r costs_l __default__List_Z) 0 <= 10000).
  { intros r col Hr. apply LegacyCosts; tauto. }
  assert (LegacyPreH1 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min2)) by paint_math.
  assert (LegacyPreH2 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) >= new_min1)) by paint_math.
  assert (LegacyPreH3 : (1 <= n_pre)) by paint_math.
  assert (LegacyPreH4 : (n_pre <= 10000)) by paint_math.
  assert (LegacyPreH5 : (2 <= k_pre)) by paint_math.
  assert (LegacyPreH6 : (k_pre <= 1000)) by paint_math.
  assert (LegacyPreH7 : ((n_pre * k_pre ) <= 1000000)) by paint_math.
  assert (LegacyPreH8 : ((Zlength (costs_l)) = n_pre)) by paint_math.
  assert (LegacyPreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) by paint_math.
  assert (LegacyPreH10 : forall (r_4: Z) , forall (col_2: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col_2)) /\ (col_2 < k_pre)) -> ((0 <= (Znth col_2 (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col_2 (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) by paint_math.
  assert (LegacyPreH11 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) by paint_math.
  assert (LegacyPreH12 : (0 <= i)) by paint_math.
  assert (LegacyPreH13 : (i < n_pre)) by paint_math.
  assert (LegacyPreH14 : (0 <= c)) by paint_math.
  assert (LegacyPreH15 : (c < k_pre)) by paint_math.
  assert (LegacyPreH16 : (0 <= prev)) by paint_math.
  assert (LegacyPreH17 : (prev <= 1000000000)) by paint_math.
  assert (LegacyPreH18 : (0 <= (Znth c (Znth i costs_l __default__List_Z) 0))) by paint_math.
  assert (LegacyPreH19 : ((Znth c (Znth i costs_l __default__List_Z) 0) <= 10000)) by paint_math.
  assert (LegacyPreH20 : ((prev + (Znth c (Znth i costs_l __default__List_Z) 0) ) <= 1000000000)) by paint_math.
  assert (LegacyPreH21 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) by paint_math.
  assert (LegacyPreH22 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) by paint_math.
  assert (LegacyPreH23 : (PaintHouseIIInnerState costs_l n_pre k_pre i c min1 min2 min1_color new_min1 new_min2 new_min1_color )) by paint_math.
  pose proof (ReusedProof.proof_of_paint_house_ii_entail_wit_5_3 k_pre n_pre costs_pre costs_l i c prev min1_color min2 min1 new_min1_color new_min2 new_min1 __default__List_Z LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20 LegacyPreH21 LegacyPreH22 LegacyPreH23) as Hreused.
  eapply derivable1_trans; [exact Hreused |].
  Intros row_ptr_reused.
  Exists row_ptr_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; paint_math.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_5 : paint_house_ii_entail_wit_5.
Proof.
  unfold paint_house_ii_entail_wit_5; try left; intros.
  pose proof ((proj1 (paint_rows_iff costs_l n_pre k_pre __default__List_Z ltac:(lia))) ltac:(assumption)) as LegacyRows.
  pose proof ((proj1 (paint_costs_iff costs_l n_pre k_pre __default__List_Z ltac:(lia) ltac:(assumption))) ltac:(split; assumption)) as LegacyCosts.
  assert (LegacyCostInput : forall r col, (((0 <= r /\ r < n_pre) /\ 0 <= col) /\ col < k_pre) ->
    0 <= Znth col (Znth r costs_l __default__List_Z) 0 <= 10000).
  { intros r col Hr. apply LegacyCosts; tauto. }
  assert (LegacyPreH1 : (1 <= n_pre)) by paint_math.
  assert (LegacyPreH2 : (n_pre <= 10000)) by paint_math.
  assert (LegacyPreH3 : (2 <= k_pre)) by paint_math.
  assert (LegacyPreH4 : (k_pre <= 1000)) by paint_math.
  assert (LegacyPreH5 : ((n_pre * k_pre ) <= 1000000)) by paint_math.
  assert (LegacyPreH6 : ((Zlength (costs_l)) = n_pre)) by paint_math.
  assert (LegacyPreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < n_pre)) -> ((Zlength ((Znth r_3 costs_l __default__List_Z))) = k_pre))) by paint_math.
  assert (LegacyPreH8 : forall (r_4: Z) , forall (col: Z) , (((((0 <= r_4) /\ (r_4 < n_pre)) /\ (0 <= col)) /\ (col < k_pre)) -> ((0 <= (Znth col (Znth r_4 costs_l __default__List_Z) 0)) /\ ((Znth col (Znth r_4 costs_l __default__List_Z) 0) <= 10000)))) by paint_math.
  assert (LegacyPreH9 : ((Zlength ((Znth i costs_l __default__List_Z))) = k_pre)) by paint_math.
  assert (LegacyPreH10 : (0 <= i)) by paint_math.
  assert (LegacyPreH11 : (i < n_pre)) by paint_math.
  assert (LegacyPreH12 : (0 <= c)) by paint_math.
  assert (LegacyPreH13 : (c < k_pre)) by paint_math.
  assert (LegacyPreH14 : (0 <= prev)) by paint_math.
  assert (LegacyPreH15 : (prev <= 1000000000)) by paint_math.
  assert (LegacyPreH16 : (0 <= total)) by paint_math.
  assert (LegacyPreH17 : (total <= 1000000000)) by paint_math.
  assert (LegacyPreH18 : (total = (prev + (Znth c (Znth i costs_l __default__List_Z) 0) ))) by paint_math.
  assert (LegacyPreH19 : (PaintHouseIIPrevSelection min1 min2 min1_color c prev )) by paint_math.
  assert (LegacyPreH20 : ((-1) <= new_min1_color)) by paint_math.
  assert (LegacyPreH21 : (new_min1_color < k_pre)) by paint_math.
  assert (LegacyPreH22 : (0 <= new_min1)) by paint_math.
  assert (LegacyPreH23 : (new_min1 <= 1000000000)) by paint_math.
  assert (LegacyPreH24 : (0 <= new_min2)) by paint_math.
  assert (LegacyPreH25 : (new_min2 <= 1000000000)) by paint_math.
  assert (LegacyPreH26 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) by paint_math.
  assert (LegacyPreH27 : (PaintHouseIIInnerState costs_l n_pre k_pre i (c + 1 ) min1 min2 min1_color new_min1 new_min2 new_min1_color )) by paint_math.
  pose proof (ReusedProof.proof_of_paint_house_ii_entail_wit_6 k_pre n_pre costs_pre costs_l row_ptr_2 i c prev total min1_color min2 min1 new_min1_color new_min1 new_min2 __default__List_Z LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20 LegacyPreH21 LegacyPreH22 LegacyPreH23 LegacyPreH24 LegacyPreH25 LegacyPreH26 LegacyPreH27) as Hreused.
  eapply derivable1_trans; [exact Hreused |].
  Intros row_ptr_reused.
  Exists row_ptr_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; paint_math.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_6 : paint_house_ii_entail_wit_6.
Proof.
  unfold paint_house_ii_entail_wit_6; left; intros.
  assert (Hck : c = k_pre) by lia.
  subst c.
  pose proof (proj2 (paint_inner_iff costs_l n_pre k_pre i k_pre min1 min2 min1_color new_min1 new_min2 new_min1_color ltac:(lia) ltac:(lia)) PreH35) as Hinner.
  pose proof (PaintHouseIIInnerState_completed_row__loop_core costs_l n_pre k_pre i min1 min2 min1_color new_min1 new_min2 new_min1_color ltac:(lia) Hinner) as Hcompleted.
  pose proof (proj1 (paint_dp_iff costs_l n_pre k_pre (i+1) new_min1 new_min2 new_min1_color ltac:(lia)) (proj2 Hcompleted)) as Hnext.
  split_pure_spatial.
  - pose proof (IntPtrArray2.missing_i_merge_to_full costs_pre i n_pre row_ptr costs_l (Znth i costs_l __default__List_Z)) as Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    rewrite sizeof_ptr.
    change (IntPtrArray2.ElemArray.full row_ptr (Zlength (Znth i costs_l __default__List_Z)) (Znth i costs_l __default__List_Z)) with (IntArray.full row_ptr (Zlength (Znth i costs_l __default__List_Z)) (Znth i costs_l __default__List_Z)) in Hmerge.
    rewrite replace_Znth_Znth in Hmerge by lia.
    eapply derivable1_trans; [|apply Hmerge; lia].
    entailer!.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.


Lemma proof_of_paint_house_ii_return_wit_1 : paint_house_ii_return_wit_1.
Proof.
  unfold paint_house_ii_return_wit_1; try left; intros.
  pose proof ((proj1 (paint_rows_iff costs_l n_pre k_pre (@nil Z) ltac:(lia))) ltac:(assumption)) as LegacyRows.
  pose proof ((proj1 (paint_costs_iff costs_l n_pre k_pre (@nil Z) ltac:(lia) ltac:(assumption))) ltac:(split; assumption)) as LegacyCosts.
  assert (LegacyCostInput : forall r col, (((0 <= r /\ r < n_pre) /\ 0 <= col) /\ col < k_pre) ->
    0 <= Znth col (Znth r costs_l (@nil Z)) 0 <= 10000).
  { intros r col Hr. apply LegacyCosts; tauto. }
  assert (LegacyPreH1 : (i >= n_pre)) by paint_math.
  assert (LegacyPreH2 : (1 <= n_pre)) by paint_math.
  assert (LegacyPreH3 : (n_pre <= 10000)) by paint_math.
  assert (LegacyPreH4 : (2 <= k_pre)) by paint_math.
  assert (LegacyPreH5 : (k_pre <= 1000)) by paint_math.
  assert (LegacyPreH6 : ((n_pre * k_pre ) <= 1000000)) by paint_math.
  assert (LegacyPreH7 : ((Zlength (costs_l)) = n_pre)) by paint_math.
  assert (LegacyPreH8 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r costs_l (@nil Z)))) = k_pre))) by paint_math.
  assert (LegacyPreH9 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < n_pre)) /\ (0 <= c)) /\ (c < k_pre)) -> ((0 <= (Znth c (Znth r_2 costs_l (@nil Z)) 0)) /\ ((Znth c (Znth r_2 costs_l (@nil Z)) 0) <= 10000)))) by paint_math.
  assert (LegacyPreH10 : (0 <= i)) by paint_math.
  assert (LegacyPreH11 : (i <= n_pre)) by paint_math.
  assert (LegacyPreH12 : ((-1) <= min1_color)) by paint_math.
  assert (LegacyPreH13 : (min1_color < k_pre)) by paint_math.
  assert (LegacyPreH14 : (0 <= min1)) by paint_math.
  assert (LegacyPreH15 : (min1 <= 1000000000)) by paint_math.
  assert (LegacyPreH16 : (0 <= min2)) by paint_math.
  assert (LegacyPreH17 : (min2 <= 1000000000)) by paint_math.
  assert (LegacyPreH18 : (PaintHouseIIDPState costs_l n_pre k_pre i min1 min2 min1_color )) by paint_math.
  pose proof (ReusedProof.proof_of_paint_house_ii_return_wit_1 k_pre n_pre costs_pre costs_l min2 min1 min1_color i (@nil Z) LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18) as Hreused.
  eapply derivable1_trans; [exact Hreused |].
  Intros.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; paint_math.
Qed.
