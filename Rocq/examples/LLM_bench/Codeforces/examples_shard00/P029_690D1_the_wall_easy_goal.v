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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P029_690D1_the_wall_easy_lib.
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
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= r_pre)) (PreH2 : (r_pre <= 100)) (PreH3 : (1 <= c_pre)) (PreH4 : (c_pre <= 100)) (PreH5 : ((Zlength (grid_data)) = r_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < r_pre)) -> ((Zlength ((Znth i grid_data __default__List_Z))) = c_pre))) (PreH7 : forall (i_2: Z) , forall (j: Z) , (((((0 <= i_2) /\ (i_2 < r_pre)) /\ (0 <= j)) /\ (j < c_pre)) -> (((Znth (j) ((Znth (i_2) (grid_data) ((@nil Z)))) (0)) = 66) \/ ((Znth (j) ((Znth (i_2) (grid_data) ((@nil Z)))) (0)) = 46)))) (PreH8 : ((Zlength (grid_mem)) = r_pre)) (PreH9 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < r_pre)) -> ((((Zlength ((Znth (i_3) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> ((Znth (j_2) ((Znth (i_3) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((Znth (i_3) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (i_3) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full ( &( "occupied" ) ) 100 (repeat_Z (0) (100)) )
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i <= r_pre)) (PreH11 : (WallColumnsAfterRows grid_data i occupied_data )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (cell: Z) (i: Z) (j: Z) (PreH1 : (1 <= r_pre)) (PreH2 : (r_pre <= 100)) (PreH3 : (1 <= c_pre)) (PreH4 : (c_pre <= 100)) (PreH5 : (Pre r_pre c_pre grid_data )) (PreH6 : ((Zlength (grid_mem)) = r_pre)) (PreH7 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH8 : (0 <= i)) (PreH9 : (i < r_pre)) (PreH10 : (0 <= j)) (PreH11 : (j < c_pre)) (PreH12 : (WallColumnsDuringRow grid_data i j occupied_data )) (PreH13 : (cell = (Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))) (PreH14 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (cell)))) ,
  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((((grid_pre + (i * (sizeof(CHAR) * 105))) + (j * sizeof(CHAR)))) # Char  |-> cell)
  **  (CharArray.mixed_missing_i (grid_pre + (i * (sizeof(CHAR) * 105))) j 0 105 (Znth (i) (grid_mem) ((@nil (@option Z)))) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
|--
  “ (66 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 66) ”
.

Definition solver_safety_wit_4 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (cell: Z) (i: Z) (j: Z) (PreH1 : (cell = 66)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i < r_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < c_pre)) (PreH13 : (WallColumnsDuringRow grid_data i j occupied_data )) (PreH14 : (cell = (Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))) (PreH15 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (cell)))) ,
  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((((grid_pre + (i * (sizeof(CHAR) * 105))) + (j * sizeof(CHAR)))) # Char  |-> cell)
  **  (CharArray.mixed_missing_i (grid_pre + (i * (sizeof(CHAR) * 105))) j 0 105 (Znth (i) (grid_mem) ((@nil (@option Z)))) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= c_pre)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i < r_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= c_pre)) (PreH13 : (WallColumnsDuringRow grid_data i j occupied_data )) ,
  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_6 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= r_pre)) (PreH2 : (r_pre <= 100)) (PreH3 : (1 <= c_pre)) (PreH4 : (c_pre <= 100)) (PreH5 : (Pre r_pre c_pre grid_data )) (PreH6 : ((Zlength (grid_mem)) = r_pre)) (PreH7 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH8 : (0 <= i)) (PreH9 : (i < r_pre)) (PreH10 : (0 <= j)) (PreH11 : (j < c_pre)) (PreH12 : (WallColumnsDuringRow grid_data i (j + 1 ) occupied_data )) ,
  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_7 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (i: Z) (PreH1 : (i >= r_pre)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i <= r_pre)) (PreH11 : (WallColumnsAfterRows grid_data i occupied_data )) ,
  ((( &( "segments" ) )) # Int  |->_)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (i: Z) (PreH1 : (i >= r_pre)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i <= r_pre)) (PreH11 : (WallColumnsAfterRows grid_data i occupied_data )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "segments" ) )) # Int  |-> 0)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (segments: Z) (j: Z) (PreH1 : ((Znth j occupied_data 0) <> 0)) (PreH2 : (j < c_pre)) (PreH3 : (1 <= r_pre)) (PreH4 : (r_pre <= 100)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 100)) (PreH7 : (Pre r_pre c_pre grid_data )) (PreH8 : ((Zlength (grid_mem)) = r_pre)) (PreH9 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH10 : (0 <= j)) (PreH11 : (j <= c_pre)) (PreH12 : (0 <= segments)) (PreH13 : (segments <= j)) (PreH14 : (WallColumnsAfterRows grid_data r_pre occupied_data )) (PreH15 : (SegmentCountPrefix grid_data j segments )) ,
  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (segments: Z) (j: Z) (PreH1 : (j <> 0)) (PreH2 : ((Znth j occupied_data 0) <> 0)) (PreH3 : (j < c_pre)) (PreH4 : (1 <= r_pre)) (PreH5 : (r_pre <= 100)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (Pre r_pre c_pre grid_data )) (PreH9 : ((Zlength (grid_mem)) = r_pre)) (PreH10 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH11 : (0 <= j)) (PreH12 : (j <= c_pre)) (PreH13 : (0 <= segments)) (PreH14 : (segments <= j)) (PreH15 : (WallColumnsAfterRows grid_data r_pre occupied_data )) (PreH16 : (SegmentCountPrefix grid_data j segments )) ,
  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (segments: Z) (j: Z) (PreH1 : (j <> 0)) (PreH2 : ((Znth j occupied_data 0) <> 0)) (PreH3 : (j < c_pre)) (PreH4 : (1 <= r_pre)) (PreH5 : (r_pre <= 100)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (Pre r_pre c_pre grid_data )) (PreH9 : ((Zlength (grid_mem)) = r_pre)) (PreH10 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH11 : (0 <= j)) (PreH12 : (j <= c_pre)) (PreH13 : (0 <= segments)) (PreH14 : (segments <= j)) (PreH15 : (WallColumnsAfterRows grid_data r_pre occupied_data )) (PreH16 : (SegmentCountPrefix grid_data j segments )) ,
  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_12 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (segments: Z) (j: Z) (PreH1 : ((Znth (j - 1 ) occupied_data 0) = 0)) (PreH2 : (j <> 0)) (PreH3 : ((Znth j occupied_data 0) <> 0)) (PreH4 : (j < c_pre)) (PreH5 : (1 <= r_pre)) (PreH6 : (r_pre <= 100)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (Pre r_pre c_pre grid_data )) (PreH10 : ((Zlength (grid_mem)) = r_pre)) (PreH11 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH12 : (0 <= j)) (PreH13 : (j <= c_pre)) (PreH14 : (0 <= segments)) (PreH15 : (segments <= j)) (PreH16 : (WallColumnsAfterRows grid_data r_pre occupied_data )) (PreH17 : (SegmentCountPrefix grid_data j segments )) ,
  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
|--
  “ ((segments + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (segments + 1 )) ”
.

Definition solver_safety_wit_13 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (segments: Z) (j: Z) (PreH1 : (j = 0)) (PreH2 : ((Znth j occupied_data 0) <> 0)) (PreH3 : (j < c_pre)) (PreH4 : (1 <= r_pre)) (PreH5 : (r_pre <= 100)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (Pre r_pre c_pre grid_data )) (PreH9 : ((Zlength (grid_mem)) = r_pre)) (PreH10 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH11 : (0 <= j)) (PreH12 : (j <= c_pre)) (PreH13 : (0 <= segments)) (PreH14 : (segments <= j)) (PreH15 : (WallColumnsAfterRows grid_data r_pre occupied_data )) (PreH16 : (SegmentCountPrefix grid_data j segments )) ,
  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
|--
  “ ((segments + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (segments + 1 )) ”
.

Definition solver_safety_wit_14 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (segments: Z) (j: Z) (PreH1 : ((Znth (j - 1 ) occupied_data 0) = 0)) (PreH2 : (j <> 0)) (PreH3 : ((Znth j occupied_data 0) <> 0)) (PreH4 : (j < c_pre)) (PreH5 : (1 <= r_pre)) (PreH6 : (r_pre <= 100)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (Pre r_pre c_pre grid_data )) (PreH10 : ((Zlength (grid_mem)) = r_pre)) (PreH11 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH12 : (0 <= j)) (PreH13 : (j <= c_pre)) (PreH14 : (0 <= segments)) (PreH15 : (segments <= j)) (PreH16 : (WallColumnsAfterRows grid_data r_pre occupied_data )) (PreH17 : (SegmentCountPrefix grid_data j segments )) ,
  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "segments" ) )) # Int  |-> (segments + 1 ))
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_15 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (segments: Z) (j: Z) (PreH1 : (j = 0)) (PreH2 : ((Znth j occupied_data 0) <> 0)) (PreH3 : (j < c_pre)) (PreH4 : (1 <= r_pre)) (PreH5 : (r_pre <= 100)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (Pre r_pre c_pre grid_data )) (PreH9 : ((Zlength (grid_mem)) = r_pre)) (PreH10 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH11 : (0 <= j)) (PreH12 : (j <= c_pre)) (PreH13 : (0 <= segments)) (PreH14 : (segments <= j)) (PreH15 : (WallColumnsAfterRows grid_data r_pre occupied_data )) (PreH16 : (SegmentCountPrefix grid_data j segments )) ,
  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "segments" ) )) # Int  |-> (segments + 1 ))
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_16 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (segments: Z) (j: Z) (PreH1 : ((Znth j occupied_data 0) = 0)) (PreH2 : (j < c_pre)) (PreH3 : (1 <= r_pre)) (PreH4 : (r_pre <= 100)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 100)) (PreH7 : (Pre r_pre c_pre grid_data )) (PreH8 : ((Zlength (grid_mem)) = r_pre)) (PreH9 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH10 : (0 <= j)) (PreH11 : (j <= c_pre)) (PreH12 : (0 <= segments)) (PreH13 : (segments <= j)) (PreH14 : (WallColumnsAfterRows grid_data r_pre occupied_data )) (PreH15 : (SegmentCountPrefix grid_data j segments )) ,
  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_17 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (segments: Z) (j: Z) (PreH1 : ((Znth (j - 1 ) occupied_data 0) <> 0)) (PreH2 : (j <> 0)) (PreH3 : ((Znth j occupied_data 0) <> 0)) (PreH4 : (j < c_pre)) (PreH5 : (1 <= r_pre)) (PreH6 : (r_pre <= 100)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (Pre r_pre c_pre grid_data )) (PreH10 : ((Zlength (grid_mem)) = r_pre)) (PreH11 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH12 : (0 <= j)) (PreH13 : (j <= c_pre)) (PreH14 : (0 <= segments)) (PreH15 : (segments <= j)) (PreH16 : (WallColumnsAfterRows grid_data r_pre occupied_data )) (PreH17 : (SegmentCountPrefix grid_data j segments )) ,
  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "segments" ) )) # Int  |-> segments)
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= r_pre)) (PreH2 : (r_pre <= 100)) (PreH3 : (1 <= c_pre)) (PreH4 : (c_pre <= 100)) (PreH5 : ((Zlength (grid_data)) = r_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < r_pre)) -> ((Zlength ((Znth i grid_data __default__List_Z))) = c_pre))) (PreH7 : forall (i_2: Z) , forall (j: Z) , (((((0 <= i_2) /\ (i_2 < r_pre)) /\ (0 <= j)) /\ (j < c_pre)) -> (((Znth (j) ((Znth (i_2) (grid_data) ((@nil Z)))) (0)) = 66) \/ ((Znth (j) ((Znth (i_2) (grid_data) ((@nil Z)))) (0)) = 46)))) (PreH8 : ((Zlength (grid_mem)) = r_pre)) (PreH9 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < r_pre)) -> ((((Zlength ((Znth (i_3) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> ((Znth (j_2) ((Znth (i_3) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((Znth (i_3) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (i_3) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (IntArray.full ( &( "occupied" ) ) 100 (repeat_Z (0) (100)) )
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
|--
  EX (occupied_data: (@list Z)) ,
  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= 100) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (Pre r_pre c_pre grid_data ) ” 
  &&  “ ((Zlength (grid_mem)) = r_pre) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= r_pre) ” 
  &&  “ (WallColumnsAfterRows grid_data 0 occupied_data ) ”
  &&  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
) \/
(
forall (c_pre: Z) (r_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= r_pre)) (PreH2 : (r_pre <= 100)) (PreH3 : (1 <= c_pre)) (PreH4 : (c_pre <= 100)) (PreH5 : ((Zlength (grid_data)) = r_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < r_pre)) -> ((Zlength ((Znth i grid_data __default__List_Z))) = c_pre))) (PreH7 : forall (i_2: Z) , forall (j: Z) , (((((0 <= i_2) /\ (i_2 < r_pre)) /\ (0 <= j)) /\ (j < c_pre)) -> (((Znth (j) ((Znth (i_2) (grid_data) ((@nil Z)))) (0)) = 66) \/ ((Znth (j) ((Znth (i_2) (grid_data) ((@nil Z)))) (0)) = 46)))) (PreH8 : ((Zlength (grid_mem)) = r_pre)) (PreH9 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < r_pre)) -> ((((Zlength ((Znth (i_3) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> ((Znth (j_2) ((Znth (i_3) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((Znth (i_3) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (i_3) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  TT && emp 
|--
  “ (WallColumnsAfterRows grid_data 0 (repeat_Z (0) (100)) ) ” 
  &&  “ (Pre r_pre c_pre grid_data ) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (c_pre: Z) (r_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= r_pre)) (PreH2 : (r_pre <= 100)) (PreH3 : (1 <= c_pre)) (PreH4 : (c_pre <= 100)) (PreH5 : ((Zlength (grid_data)) = r_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < r_pre)) -> ((Zlength ((Znth i grid_data __default__List_Z))) = c_pre))) (PreH7 : forall (i_2: Z) , forall (j: Z) , (((((0 <= i_2) /\ (i_2 < r_pre)) /\ (0 <= j)) /\ (j < c_pre)) -> (((Znth (j) ((Znth (i_2) (grid_data) ((@nil Z)))) (0)) = 66) \/ ((Znth (j) ((Znth (i_2) (grid_data) ((@nil Z)))) (0)) = 46)))) (PreH8 : ((Zlength (grid_mem)) = r_pre)) (PreH9 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < r_pre)) -> ((((Zlength ((Znth (i_3) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> ((Znth (j_2) ((Znth (i_3) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((Znth (i_3) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (i_3) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (WallColumnsAfterRows grid_data 0 (repeat_Z (0) (100)) )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (c_pre: Z) (r_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= r_pre)) (PreH2 : (r_pre <= 100)) (PreH3 : (1 <= c_pre)) (PreH4 : (c_pre <= 100)) (PreH5 : ((Zlength (grid_data)) = r_pre)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < r_pre)) -> ((Zlength ((Znth i grid_data __default__List_Z))) = c_pre))) (PreH7 : forall (i_2: Z) , forall (j: Z) , (((((0 <= i_2) /\ (i_2 < r_pre)) /\ (0 <= j)) /\ (j < c_pre)) -> (((Znth (j) ((Znth (i_2) (grid_data) ((@nil Z)))) (0)) = 66) \/ ((Znth (j) ((Znth (i_2) (grid_data) ((@nil Z)))) (0)) = 46)))) (PreH8 : ((Zlength (grid_mem)) = r_pre)) (PreH9 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < r_pre)) -> ((((Zlength ((Znth (i_3) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> ((Znth (j_2) ((Znth (i_3) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((Znth (i_3) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (i_3) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (Pre r_pre c_pre grid_data )
.

Definition solver_entail_wit_2 := 
(
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i <= r_pre)) (PreH11 : (WallColumnsAfterRows grid_data i occupied_data_2 )) ,
  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data_2 )
|--
  EX (occupied_data: (@list Z)) ,
  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= 100) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (Pre r_pre c_pre grid_data ) ” 
  &&  “ ((Zlength (grid_mem)) = r_pre) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (WallColumnsDuringRow grid_data i 0 occupied_data ) ”
  &&  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
) \/
(
forall (c_pre: Z) (r_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i <= r_pre)) (PreH11 : (WallColumnsAfterRows grid_data i occupied_data_2 )) ,
  TT && emp 
|--
  “ (WallColumnsDuringRow grid_data i 0 occupied_data_2 ) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (c_pre: Z) (r_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (i: Z) (PreH1 : (i < r_pre)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i <= r_pre)) (PreH11 : (WallColumnsAfterRows grid_data i occupied_data_2 )) ,
  (WallColumnsDuringRow grid_data i 0 occupied_data_2 )
.

Definition solver_entail_wit_3 := 
(
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < c_pre)) (PreH5 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))))) (PreH6 : (j < c_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= 100)) (PreH9 : (1 <= c_pre)) (PreH10 : (c_pre <= 100)) (PreH11 : (Pre r_pre c_pre grid_data )) (PreH12 : ((Zlength (grid_mem)) = r_pre)) (PreH13 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH14 : (0 <= i)) (PreH15 : (i < r_pre)) (PreH16 : (0 <= j)) (PreH17 : (j <= c_pre)) (PreH18 : (WallColumnsDuringRow grid_data i j occupied_data_2 )) ,
  (CharArray2.mixed_full grid_pre r_pre 105 (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data_2 )
|--
  EX (cell: Z)  (occupied_data: (@list Z)) ,
  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= 100) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (Pre r_pre c_pre grid_data ) ” 
  &&  “ ((Zlength (grid_mem)) = r_pre) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < c_pre) ” 
  &&  “ (WallColumnsDuringRow grid_data i j occupied_data ) ” 
  &&  “ (cell = (Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0))) ” 
  &&  “ ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (cell))) ”
  &&  ((((grid_pre + (i * (sizeof(CHAR) * 105))) + (j * sizeof(CHAR)))) # Char  |-> cell)
  **  (CharArray.mixed_missing_i (grid_pre + (i * (sizeof(CHAR) * 105))) j 0 105 (Znth (i) (grid_mem) ((@nil (@option Z)))) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
) \/
(
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (j: Z) (i: Z)  __default__List__App_option_Z (PreH1 : (0 <= i)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < c_pre)) (PreH5 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))))) (PreH6 : (j < c_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= 100)) (PreH9 : (1 <= c_pre)) (PreH10 : (c_pre <= 100)) (PreH11 : (Pre r_pre c_pre grid_data )) (PreH12 : ((Zlength (grid_mem)) = r_pre)) (PreH13 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH14 : (0 <= i)) (PreH15 : (i < r_pre)) (PreH16 : (0 <= j)) (PreH17 : (j <= c_pre)) (PreH18 : (WallColumnsDuringRow grid_data i j occupied_data_2 )) ,
  (CharArray.mixed_missing_i (grid_pre + (i * (sizeof(CHAR) * 105))) j 0 105 (Znth i (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) __default__List__App_option_Z) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) )
|--
  “ ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Array2.mixed_val ((Znth i (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) __default__List__App_option_Z)) (j))))) ” 
  &&  “ ((Array2.mixed_val ((Znth i (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) __default__List__App_option_Z)) (j)) = (Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0))) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (Array2.mixed_def (Znth i (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) __default__List__App_option_Z) j ) ”
  &&  (CharArray.mixed_missing_i (grid_pre + (i * (sizeof(CHAR) * 105))) j 0 105 (Znth (i) (grid_mem) ((@nil (@option Z)))) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 grid_mem )
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (j: Z) (i: Z)  __default__List__App_option_Z (PreH1 : (0 <= i)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < c_pre)) (PreH5 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))))) (PreH6 : (j < c_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= 100)) (PreH9 : (1 <= c_pre)) (PreH10 : (c_pre <= 100)) (PreH11 : (Pre r_pre c_pre grid_data )) (PreH12 : ((Zlength (grid_mem)) = r_pre)) (PreH13 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH14 : (0 <= i)) (PreH15 : (i < r_pre)) (PreH16 : (0 <= j)) (PreH17 : (j <= c_pre)) (PreH18 : (WallColumnsDuringRow grid_data i j occupied_data_2 )) ,
  (CharArray.mixed_missing_i (grid_pre + (i * (sizeof(CHAR) * 105))) j 0 105 (Znth i (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) __default__List__App_option_Z) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) )
|--
  “ ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Array2.mixed_val ((Znth i (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) __default__List__App_option_Z)) (j))))) ”
.

Definition solver_entail_wit_3_split_goal_2 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (j: Z) (i: Z)  __default__List__App_option_Z (PreH1 : (0 <= i)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < c_pre)) (PreH5 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))))) (PreH6 : (j < c_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= 100)) (PreH9 : (1 <= c_pre)) (PreH10 : (c_pre <= 100)) (PreH11 : (Pre r_pre c_pre grid_data )) (PreH12 : ((Zlength (grid_mem)) = r_pre)) (PreH13 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH14 : (0 <= i)) (PreH15 : (i < r_pre)) (PreH16 : (0 <= j)) (PreH17 : (j <= c_pre)) (PreH18 : (WallColumnsDuringRow grid_data i j occupied_data_2 )) ,
  (CharArray.mixed_missing_i (grid_pre + (i * (sizeof(CHAR) * 105))) j 0 105 (Znth i (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) __default__List__App_option_Z) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) )
|--
  “ ((Array2.mixed_val ((Znth i (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) __default__List__App_option_Z)) (j)) = (Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0))) ”
.

Definition solver_entail_wit_3_split_goal_3 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (j: Z) (i: Z)  __default__List__App_option_Z (PreH1 : (0 <= i)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < c_pre)) (PreH5 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))))) (PreH6 : (j < c_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= 100)) (PreH9 : (1 <= c_pre)) (PreH10 : (c_pre <= 100)) (PreH11 : (Pre r_pre c_pre grid_data )) (PreH12 : ((Zlength (grid_mem)) = r_pre)) (PreH13 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH14 : (0 <= i)) (PreH15 : (i < r_pre)) (PreH16 : (0 <= j)) (PreH17 : (j <= c_pre)) (PreH18 : (WallColumnsDuringRow grid_data i j occupied_data_2 )) ,
  (CharArray.mixed_missing_i (grid_pre + (i * (sizeof(CHAR) * 105))) j 0 105 (Znth i (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) __default__List__App_option_Z) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) )
|--
  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ”
.

Definition solver_entail_wit_3_split_goal_4 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (j: Z) (i: Z)  __default__List__App_option_Z (PreH1 : (0 <= i)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < c_pre)) (PreH5 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))))) (PreH6 : (j < c_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= 100)) (PreH9 : (1 <= c_pre)) (PreH10 : (c_pre <= 100)) (PreH11 : (Pre r_pre c_pre grid_data )) (PreH12 : ((Zlength (grid_mem)) = r_pre)) (PreH13 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH14 : (0 <= i)) (PreH15 : (i < r_pre)) (PreH16 : (0 <= j)) (PreH17 : (j <= c_pre)) (PreH18 : (WallColumnsDuringRow grid_data i j occupied_data_2 )) ,
  (CharArray.mixed_missing_i (grid_pre + (i * (sizeof(CHAR) * 105))) j 0 105 (Znth i (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) __default__List__App_option_Z) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) )
|--
  “ (Array2.mixed_def (Znth i (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) __default__List__App_option_Z) j ) ”
.

Definition solver_entail_wit_3_split_goal_spatial := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (j: Z) (i: Z)  __default__List__App_option_Z (PreH1 : (0 <= i)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < c_pre)) (PreH5 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))))) (PreH6 : (j < c_pre)) (PreH7 : (1 <= r_pre)) (PreH8 : (r_pre <= 100)) (PreH9 : (1 <= c_pre)) (PreH10 : (c_pre <= 100)) (PreH11 : (Pre r_pre c_pre grid_data )) (PreH12 : ((Zlength (grid_mem)) = r_pre)) (PreH13 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH14 : (0 <= i)) (PreH15 : (i < r_pre)) (PreH16 : (0 <= j)) (PreH17 : (j <= c_pre)) (PreH18 : (WallColumnsDuringRow grid_data i j occupied_data_2 )) ,
  (CharArray.mixed_missing_i (grid_pre + (i * (sizeof(CHAR) * 105))) j 0 105 (Znth i (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) __default__List__App_option_Z) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) )
|--
  (CharArray.mixed_missing_i (grid_pre + (i * (sizeof(CHAR) * 105))) j 0 105 (Znth (i) (grid_mem) ((@nil (@option Z)))) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 grid_mem )
.

Definition solver_entail_wit_4_1 := 
(
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (cell: Z) (i: Z) (j: Z) (PreH1 : (cell = 66)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i < r_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < c_pre)) (PreH13 : (WallColumnsDuringRow grid_data i j occupied_data_2 )) (PreH14 : (cell = (Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))) (PreH15 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (cell)))) ,
  (IntArray.full ( &( "occupied" ) ) 100 (replace_Znth (j) (1) (occupied_data_2)) )
  **  (CharArray2.mixed_full grid_pre r_pre 105 (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) )
|--
  EX (occupied_data: (@list Z)) ,
  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= 100) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (Pre r_pre c_pre grid_data ) ” 
  &&  “ ((Zlength (grid_mem)) = r_pre) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < c_pre) ” 
  &&  “ (WallColumnsDuringRow grid_data i (j + 1 ) occupied_data ) ”
  &&  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
) \/
(
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (cell: Z) (i: Z) (j: Z) (PreH1 : (cell = 66)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i < r_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < c_pre)) (PreH13 : (WallColumnsDuringRow grid_data i j occupied_data_2 )) (PreH14 : (cell = (Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))) (PreH15 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (cell)))) ,
  (CharArray2.mixed_full grid_pre r_pre 105 (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) )
|--
  “ (WallColumnsDuringRow grid_data i (j + 1 ) (replace_Znth (j) (1) (occupied_data_2)) ) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ”
  &&  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
).

Definition solver_entail_wit_4_1_split_goal_1 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (cell: Z) (i: Z) (j: Z) (PreH1 : (cell = 66)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i < r_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < c_pre)) (PreH13 : (WallColumnsDuringRow grid_data i j occupied_data_2 )) (PreH14 : (cell = (Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))) (PreH15 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (cell)))) ,
  (CharArray2.mixed_full grid_pre r_pre 105 (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) )
|--
  “ (WallColumnsDuringRow grid_data i (j + 1 ) (replace_Znth (j) (1) (occupied_data_2)) ) ”
.

Definition solver_entail_wit_4_1_split_goal_2 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (cell: Z) (i: Z) (j: Z) (PreH1 : (cell = 66)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i < r_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < c_pre)) (PreH13 : (WallColumnsDuringRow grid_data i j occupied_data_2 )) (PreH14 : (cell = (Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))) (PreH15 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (cell)))) ,
  (CharArray2.mixed_full grid_pre r_pre 105 (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) )
|--
  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ”
.

Definition solver_entail_wit_4_1_split_goal_spatial := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (cell: Z) (i: Z) (j: Z) (PreH1 : (cell = 66)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i < r_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < c_pre)) (PreH13 : (WallColumnsDuringRow grid_data i j occupied_data_2 )) (PreH14 : (cell = (Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))) (PreH15 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (cell)))) ,
  (CharArray2.mixed_full grid_pre r_pre 105 (Array2.replace_mixed_row (i) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (grid_mem)) )
|--
  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
.

Definition solver_entail_wit_4_2 := 
(
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (cell: Z) (i: Z) (j: Z) (PreH1 : (cell <> 66)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i < r_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < c_pre)) (PreH13 : (WallColumnsDuringRow grid_data i j occupied_data_2 )) (PreH14 : (cell = (Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))) (PreH15 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (cell)))) ,
  ((((grid_pre + (i * (sizeof(CHAR) * 105))) + (j * sizeof(CHAR)))) # Char  |-> cell)
  **  (CharArray.mixed_missing_i (grid_pre + (i * (sizeof(CHAR) * 105))) j 0 105 (Znth (i) (grid_mem) ((@nil (@option Z)))) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data_2 )
|--
  EX (occupied_data: (@list Z)) ,
  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= 100) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (Pre r_pre c_pre grid_data ) ” 
  &&  “ ((Zlength (grid_mem)) = r_pre) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < c_pre) ” 
  &&  “ (WallColumnsDuringRow grid_data i (j + 1 ) occupied_data ) ”
  &&  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
) \/
(
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (cell: Z) (i: Z) (j: Z) (PreH1 : (cell <> 66)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i < r_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < c_pre)) (PreH13 : (WallColumnsDuringRow grid_data i j occupied_data_2 )) (PreH14 : (cell = (Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))) (PreH15 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (cell)))) ,
  ((((grid_pre + (i * (sizeof(CHAR) * 105))) + (j * sizeof(CHAR)))) # Char  |-> cell)
  **  (CharArray.mixed_missing_i (grid_pre + (i * (sizeof(CHAR) * 105))) j 0 105 (Znth (i) (grid_mem) ((@nil (@option Z)))) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 grid_mem )
|--
  “ (WallColumnsDuringRow grid_data i (j + 1 ) occupied_data_2 ) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ”
  &&  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
).

Definition solver_entail_wit_4_2_split_goal_1 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (cell: Z) (i: Z) (j: Z) (PreH1 : (cell <> 66)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i < r_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < c_pre)) (PreH13 : (WallColumnsDuringRow grid_data i j occupied_data_2 )) (PreH14 : (cell = (Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))) (PreH15 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (cell)))) ,
  ((((grid_pre + (i * (sizeof(CHAR) * 105))) + (j * sizeof(CHAR)))) # Char  |-> cell)
  **  (CharArray.mixed_missing_i (grid_pre + (i * (sizeof(CHAR) * 105))) j 0 105 (Znth (i) (grid_mem) ((@nil (@option Z)))) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 grid_mem )
|--
  “ (WallColumnsDuringRow grid_data i (j + 1 ) occupied_data_2 ) ”
.

Definition solver_entail_wit_4_2_split_goal_2 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (cell: Z) (i: Z) (j: Z) (PreH1 : (cell <> 66)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i < r_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < c_pre)) (PreH13 : (WallColumnsDuringRow grid_data i j occupied_data_2 )) (PreH14 : (cell = (Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))) (PreH15 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (cell)))) ,
  ((((grid_pre + (i * (sizeof(CHAR) * 105))) + (j * sizeof(CHAR)))) # Char  |-> cell)
  **  (CharArray.mixed_missing_i (grid_pre + (i * (sizeof(CHAR) * 105))) j 0 105 (Znth (i) (grid_mem) ((@nil (@option Z)))) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 grid_mem )
|--
  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ”
.

Definition solver_entail_wit_4_2_split_goal_spatial := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (cell: Z) (i: Z) (j: Z) (PreH1 : (cell <> 66)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i < r_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < c_pre)) (PreH13 : (WallColumnsDuringRow grid_data i j occupied_data_2 )) (PreH14 : (cell = (Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))) (PreH15 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (cell)))) ,
  ((((grid_pre + (i * (sizeof(CHAR) * 105))) + (j * sizeof(CHAR)))) # Char  |-> cell)
  **  (CharArray.mixed_missing_i (grid_pre + (i * (sizeof(CHAR) * 105))) j 0 105 (Znth (i) (grid_mem) ((@nil (@option Z)))) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 grid_mem )
|--
  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
.

Definition solver_entail_wit_5 := 
(
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= c_pre)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i < r_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= c_pre)) (PreH13 : (WallColumnsDuringRow grid_data i j occupied_data_2 )) ,
  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data_2 )
|--
  EX (occupied_data: (@list Z)) ,
  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= 100) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (Pre r_pre c_pre grid_data ) ” 
  &&  “ ((Zlength (grid_mem)) = r_pre) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= r_pre) ” 
  &&  “ (WallColumnsAfterRows grid_data (i + 1 ) occupied_data ) ”
  &&  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
) \/
(
forall (c_pre: Z) (r_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= c_pre)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i < r_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= c_pre)) (PreH13 : (WallColumnsDuringRow grid_data i j occupied_data_2 )) ,
  TT && emp 
|--
  “ (WallColumnsAfterRows grid_data (i + 1 ) occupied_data_2 ) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 := 
forall (c_pre: Z) (r_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= c_pre)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i < r_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= c_pre)) (PreH13 : (WallColumnsDuringRow grid_data i j occupied_data_2 )) ,
  (WallColumnsAfterRows grid_data (i + 1 ) occupied_data_2 )
.

Definition solver_entail_wit_6 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= r_pre)) (PreH2 : (r_pre <= 100)) (PreH3 : (1 <= c_pre)) (PreH4 : (c_pre <= 100)) (PreH5 : (Pre r_pre c_pre grid_data )) (PreH6 : ((Zlength (grid_mem)) = r_pre)) (PreH7 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH8 : (0 <= i)) (PreH9 : (i < r_pre)) (PreH10 : (0 <= j)) (PreH11 : (j < c_pre)) (PreH12 : (WallColumnsDuringRow grid_data i (j + 1 ) occupied_data_2 )) ,
  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data_2 )
|--
  EX (occupied_data: (@list Z)) ,
  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= 100) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (Pre r_pre c_pre grid_data ) ” 
  &&  “ ((Zlength (grid_mem)) = r_pre) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= c_pre) ” 
  &&  “ (WallColumnsDuringRow grid_data i (j + 1 ) occupied_data ) ”
  &&  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
.

Definition solver_entail_wit_7 := 
(
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (i: Z) (PreH1 : (i >= r_pre)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i <= r_pre)) (PreH11 : (WallColumnsAfterRows grid_data i occupied_data_2 )) ,
  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data_2 )
|--
  EX (occupied_data: (@list Z)) ,
  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= 100) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (Pre r_pre c_pre grid_data ) ” 
  &&  “ ((Zlength (grid_mem)) = r_pre) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (WallColumnsAfterRows grid_data r_pre occupied_data ) ” 
  &&  “ (SegmentCountPrefix grid_data 0 0 ) ”
  &&  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
) \/
(
forall (c_pre: Z) (r_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (i: Z) (PreH1 : (i >= r_pre)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i <= r_pre)) (PreH11 : (WallColumnsAfterRows grid_data i occupied_data_2 )) ,
  TT && emp 
|--
  “ (SegmentCountPrefix grid_data 0 0 ) ” 
  &&  “ (WallColumnsAfterRows grid_data r_pre occupied_data_2 ) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 := 
forall (c_pre: Z) (r_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (i: Z) (PreH1 : (i >= r_pre)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i <= r_pre)) (PreH11 : (WallColumnsAfterRows grid_data i occupied_data_2 )) ,
  (SegmentCountPrefix grid_data 0 0 )
.

Definition solver_entail_wit_7_split_goal_2 := 
forall (c_pre: Z) (r_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (i: Z) (PreH1 : (i >= r_pre)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < r_pre)) -> ((((Zlength ((Znth (row_2) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < c_pre)) -> ((Znth (col_2) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row_2) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i <= r_pre)) (PreH11 : (WallColumnsAfterRows grid_data i occupied_data_2 )) ,
  (WallColumnsAfterRows grid_data r_pre occupied_data_2 )
.

Definition solver_entail_wit_8_1 := 
(
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (segments: Z) (j: Z) (PreH1 : ((Znth (j - 1 ) occupied_data_2 0) = 0)) (PreH2 : (j <> 0)) (PreH3 : ((Znth j occupied_data_2 0) <> 0)) (PreH4 : (j < c_pre)) (PreH5 : (1 <= r_pre)) (PreH6 : (r_pre <= 100)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (Pre r_pre c_pre grid_data )) (PreH10 : ((Zlength (grid_mem)) = r_pre)) (PreH11 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH12 : (0 <= j)) (PreH13 : (j <= c_pre)) (PreH14 : (0 <= segments)) (PreH15 : (segments <= j)) (PreH16 : (WallColumnsAfterRows grid_data r_pre occupied_data_2 )) (PreH17 : (SegmentCountPrefix grid_data j segments )) ,
  (IntArray.full ( &( "occupied" ) ) 100 occupied_data_2 )
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
|--
  EX (occupied_data: (@list Z)) ,
  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= 100) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (Pre r_pre c_pre grid_data ) ” 
  &&  “ ((Zlength (grid_mem)) = r_pre) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= c_pre) ” 
  &&  “ (0 <= (segments + 1 )) ” 
  &&  “ ((segments + 1 ) <= (j + 1 )) ” 
  &&  “ (WallColumnsAfterRows grid_data r_pre occupied_data ) ” 
  &&  “ (SegmentCountPrefix grid_data (j + 1 ) (segments + 1 ) ) ”
  &&  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
) \/
(
forall (c_pre: Z) (r_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (segments: Z) (j: Z) (PreH1 : ((Znth (j - 1 ) occupied_data_2 0) = 0)) (PreH2 : (j <> 0)) (PreH3 : ((Znth j occupied_data_2 0) <> 0)) (PreH4 : (j < c_pre)) (PreH5 : (1 <= r_pre)) (PreH6 : (r_pre <= 100)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (Pre r_pre c_pre grid_data )) (PreH10 : ((Zlength (grid_mem)) = r_pre)) (PreH11 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH12 : (0 <= j)) (PreH13 : (j <= c_pre)) (PreH14 : (0 <= segments)) (PreH15 : (segments <= j)) (PreH16 : (WallColumnsAfterRows grid_data r_pre occupied_data_2 )) (PreH17 : (SegmentCountPrefix grid_data j segments )) ,
  TT && emp 
|--
  “ (SegmentCountPrefix grid_data (j + 1 ) (segments + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_8_1_split_goal_1 := 
forall (c_pre: Z) (r_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (segments: Z) (j: Z) (PreH1 : ((Znth (j - 1 ) occupied_data_2 0) = 0)) (PreH2 : (j <> 0)) (PreH3 : ((Znth j occupied_data_2 0) <> 0)) (PreH4 : (j < c_pre)) (PreH5 : (1 <= r_pre)) (PreH6 : (r_pre <= 100)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (Pre r_pre c_pre grid_data )) (PreH10 : ((Zlength (grid_mem)) = r_pre)) (PreH11 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH12 : (0 <= j)) (PreH13 : (j <= c_pre)) (PreH14 : (0 <= segments)) (PreH15 : (segments <= j)) (PreH16 : (WallColumnsAfterRows grid_data r_pre occupied_data_2 )) (PreH17 : (SegmentCountPrefix grid_data j segments )) ,
  (SegmentCountPrefix grid_data (j + 1 ) (segments + 1 ) )
.

Definition solver_entail_wit_8_2 := 
(
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (segments: Z) (j: Z) (PreH1 : (j = 0)) (PreH2 : ((Znth j occupied_data_2 0) <> 0)) (PreH3 : (j < c_pre)) (PreH4 : (1 <= r_pre)) (PreH5 : (r_pre <= 100)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (Pre r_pre c_pre grid_data )) (PreH9 : ((Zlength (grid_mem)) = r_pre)) (PreH10 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH11 : (0 <= j)) (PreH12 : (j <= c_pre)) (PreH13 : (0 <= segments)) (PreH14 : (segments <= j)) (PreH15 : (WallColumnsAfterRows grid_data r_pre occupied_data_2 )) (PreH16 : (SegmentCountPrefix grid_data j segments )) ,
  (IntArray.full ( &( "occupied" ) ) 100 occupied_data_2 )
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
|--
  EX (occupied_data: (@list Z)) ,
  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= 100) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (Pre r_pre c_pre grid_data ) ” 
  &&  “ ((Zlength (grid_mem)) = r_pre) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= c_pre) ” 
  &&  “ (0 <= (segments + 1 )) ” 
  &&  “ ((segments + 1 ) <= (j + 1 )) ” 
  &&  “ (WallColumnsAfterRows grid_data r_pre occupied_data ) ” 
  &&  “ (SegmentCountPrefix grid_data (j + 1 ) (segments + 1 ) ) ”
  &&  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
) \/
(
forall (c_pre: Z) (r_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (segments: Z) (j: Z) (PreH1 : (j = 0)) (PreH2 : ((Znth j occupied_data_2 0) <> 0)) (PreH3 : (j < c_pre)) (PreH4 : (1 <= r_pre)) (PreH5 : (r_pre <= 100)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (Pre r_pre c_pre grid_data )) (PreH9 : ((Zlength (grid_mem)) = r_pre)) (PreH10 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH11 : (0 <= j)) (PreH12 : (j <= c_pre)) (PreH13 : (0 <= segments)) (PreH14 : (segments <= j)) (PreH15 : (WallColumnsAfterRows grid_data r_pre occupied_data_2 )) (PreH16 : (SegmentCountPrefix grid_data j segments )) ,
  TT && emp 
|--
  “ (SegmentCountPrefix grid_data (0 + 1 ) (segments + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_8_2_split_goal_1 := 
forall (c_pre: Z) (r_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (segments: Z) (j: Z) (PreH1 : (j = 0)) (PreH2 : ((Znth j occupied_data_2 0) <> 0)) (PreH3 : (j < c_pre)) (PreH4 : (1 <= r_pre)) (PreH5 : (r_pre <= 100)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (Pre r_pre c_pre grid_data )) (PreH9 : ((Zlength (grid_mem)) = r_pre)) (PreH10 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH11 : (0 <= j)) (PreH12 : (j <= c_pre)) (PreH13 : (0 <= segments)) (PreH14 : (segments <= j)) (PreH15 : (WallColumnsAfterRows grid_data r_pre occupied_data_2 )) (PreH16 : (SegmentCountPrefix grid_data j segments )) ,
  (SegmentCountPrefix grid_data (0 + 1 ) (segments + 1 ) )
.

Definition solver_entail_wit_8_3 := 
(
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (segments: Z) (j: Z) (PreH1 : ((Znth j occupied_data_2 0) = 0)) (PreH2 : (j < c_pre)) (PreH3 : (1 <= r_pre)) (PreH4 : (r_pre <= 100)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 100)) (PreH7 : (Pre r_pre c_pre grid_data )) (PreH8 : ((Zlength (grid_mem)) = r_pre)) (PreH9 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH10 : (0 <= j)) (PreH11 : (j <= c_pre)) (PreH12 : (0 <= segments)) (PreH13 : (segments <= j)) (PreH14 : (WallColumnsAfterRows grid_data r_pre occupied_data_2 )) (PreH15 : (SegmentCountPrefix grid_data j segments )) ,
  (IntArray.full ( &( "occupied" ) ) 100 occupied_data_2 )
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
|--
  EX (occupied_data: (@list Z)) ,
  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= 100) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (Pre r_pre c_pre grid_data ) ” 
  &&  “ ((Zlength (grid_mem)) = r_pre) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= c_pre) ” 
  &&  “ (0 <= segments) ” 
  &&  “ (segments <= (j + 1 )) ” 
  &&  “ (WallColumnsAfterRows grid_data r_pre occupied_data ) ” 
  &&  “ (SegmentCountPrefix grid_data (j + 1 ) segments ) ”
  &&  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
) \/
(
forall (c_pre: Z) (r_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (segments: Z) (j: Z) (PreH1 : ((Znth j occupied_data_2 0) = 0)) (PreH2 : (j < c_pre)) (PreH3 : (1 <= r_pre)) (PreH4 : (r_pre <= 100)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 100)) (PreH7 : (Pre r_pre c_pre grid_data )) (PreH8 : ((Zlength (grid_mem)) = r_pre)) (PreH9 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH10 : (0 <= j)) (PreH11 : (j <= c_pre)) (PreH12 : (0 <= segments)) (PreH13 : (segments <= j)) (PreH14 : (WallColumnsAfterRows grid_data r_pre occupied_data_2 )) (PreH15 : (SegmentCountPrefix grid_data j segments )) ,
  TT && emp 
|--
  “ (SegmentCountPrefix grid_data (j + 1 ) segments ) ”
  &&  emp
).

Definition solver_entail_wit_8_3_split_goal_1 := 
forall (c_pre: Z) (r_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (segments: Z) (j: Z) (PreH1 : ((Znth j occupied_data_2 0) = 0)) (PreH2 : (j < c_pre)) (PreH3 : (1 <= r_pre)) (PreH4 : (r_pre <= 100)) (PreH5 : (1 <= c_pre)) (PreH6 : (c_pre <= 100)) (PreH7 : (Pre r_pre c_pre grid_data )) (PreH8 : ((Zlength (grid_mem)) = r_pre)) (PreH9 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH10 : (0 <= j)) (PreH11 : (j <= c_pre)) (PreH12 : (0 <= segments)) (PreH13 : (segments <= j)) (PreH14 : (WallColumnsAfterRows grid_data r_pre occupied_data_2 )) (PreH15 : (SegmentCountPrefix grid_data j segments )) ,
  (SegmentCountPrefix grid_data (j + 1 ) segments )
.

Definition solver_entail_wit_8_4 := 
(
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (segments: Z) (j: Z) (PreH1 : ((Znth (j - 1 ) occupied_data_2 0) <> 0)) (PreH2 : (j <> 0)) (PreH3 : ((Znth j occupied_data_2 0) <> 0)) (PreH4 : (j < c_pre)) (PreH5 : (1 <= r_pre)) (PreH6 : (r_pre <= 100)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (Pre r_pre c_pre grid_data )) (PreH10 : ((Zlength (grid_mem)) = r_pre)) (PreH11 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH12 : (0 <= j)) (PreH13 : (j <= c_pre)) (PreH14 : (0 <= segments)) (PreH15 : (segments <= j)) (PreH16 : (WallColumnsAfterRows grid_data r_pre occupied_data_2 )) (PreH17 : (SegmentCountPrefix grid_data j segments )) ,
  (IntArray.full ( &( "occupied" ) ) 100 occupied_data_2 )
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
|--
  EX (occupied_data: (@list Z)) ,
  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= 100) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (Pre r_pre c_pre grid_data ) ” 
  &&  “ ((Zlength (grid_mem)) = r_pre) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= c_pre) ” 
  &&  “ (0 <= segments) ” 
  &&  “ (segments <= (j + 1 )) ” 
  &&  “ (WallColumnsAfterRows grid_data r_pre occupied_data ) ” 
  &&  “ (SegmentCountPrefix grid_data (j + 1 ) segments ) ”
  &&  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
) \/
(
forall (c_pre: Z) (r_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (segments: Z) (j: Z) (PreH1 : ((Znth (j - 1 ) occupied_data_2 0) <> 0)) (PreH2 : (j <> 0)) (PreH3 : ((Znth j occupied_data_2 0) <> 0)) (PreH4 : (j < c_pre)) (PreH5 : (1 <= r_pre)) (PreH6 : (r_pre <= 100)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (Pre r_pre c_pre grid_data )) (PreH10 : ((Zlength (grid_mem)) = r_pre)) (PreH11 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH12 : (0 <= j)) (PreH13 : (j <= c_pre)) (PreH14 : (0 <= segments)) (PreH15 : (segments <= j)) (PreH16 : (WallColumnsAfterRows grid_data r_pre occupied_data_2 )) (PreH17 : (SegmentCountPrefix grid_data j segments )) ,
  TT && emp 
|--
  “ (SegmentCountPrefix grid_data (j + 1 ) segments ) ”
  &&  emp
).

Definition solver_entail_wit_8_4_split_goal_1 := 
forall (c_pre: Z) (r_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data_2: (@list Z)) (segments: Z) (j: Z) (PreH1 : ((Znth (j - 1 ) occupied_data_2 0) <> 0)) (PreH2 : (j <> 0)) (PreH3 : ((Znth j occupied_data_2 0) <> 0)) (PreH4 : (j < c_pre)) (PreH5 : (1 <= r_pre)) (PreH6 : (r_pre <= 100)) (PreH7 : (1 <= c_pre)) (PreH8 : (c_pre <= 100)) (PreH9 : (Pre r_pre c_pre grid_data )) (PreH10 : ((Zlength (grid_mem)) = r_pre)) (PreH11 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH12 : (0 <= j)) (PreH13 : (j <= c_pre)) (PreH14 : (0 <= segments)) (PreH15 : (segments <= j)) (PreH16 : (WallColumnsAfterRows grid_data r_pre occupied_data_2 )) (PreH17 : (SegmentCountPrefix grid_data j segments )) ,
  (SegmentCountPrefix grid_data (j + 1 ) segments )
.

Definition solver_return_wit_1 := 
(
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (segments: Z) (j: Z) (PreH1 : (j >= c_pre)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= j)) (PreH10 : (j <= c_pre)) (PreH11 : (0 <= segments)) (PreH12 : (segments <= j)) (PreH13 : (WallColumnsAfterRows grid_data r_pre occupied_data )) (PreH14 : (SegmentCountPrefix grid_data j segments )) ,
  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
|--
  “ (Spec r_pre c_pre grid_data segments ) ”
  &&  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
) \/
(
forall (c_pre: Z) (r_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (segments: Z) (j: Z) (PreH1 : (j >= c_pre)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= j)) (PreH10 : (j <= c_pre)) (PreH11 : (0 <= segments)) (PreH12 : (segments <= j)) (PreH13 : (WallColumnsAfterRows grid_data r_pre occupied_data )) (PreH14 : (SegmentCountPrefix grid_data j segments )) ,
  TT && emp 
|--
  “ (Spec r_pre c_pre grid_data segments ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (c_pre: Z) (r_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (segments: Z) (j: Z) (PreH1 : (j >= c_pre)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= j)) (PreH10 : (j <= c_pre)) (PreH11 : (0 <= segments)) (PreH12 : (segments <= j)) (PreH13 : (WallColumnsAfterRows grid_data r_pre occupied_data )) (PreH14 : (SegmentCountPrefix grid_data j segments )) ,
  (Spec r_pre c_pre grid_data segments )
.

Definition solver_partial_solve_wit_1_pure := 
(
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < c_pre)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i < r_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= c_pre)) (PreH13 : (WallColumnsDuringRow grid_data i j occupied_data )) ,
  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
|--
  “ (0 <= i) ” 
  &&  “ (i < r_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < c_pre) ” 
  &&  “ ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0))))) ”
) \/
(
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (c_pre <= INT_MAX)) (PreH4 : (r_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (c_pre >= INT_MIN)) (PreH8 : (r_pre >= INT_MIN)) (PreH9 : (j < c_pre)) (PreH10 : (1 <= r_pre)) (PreH11 : (r_pre <= 100)) (PreH12 : (1 <= c_pre)) (PreH13 : (c_pre <= 100)) (PreH14 : (Pre r_pre c_pre grid_data )) (PreH15 : ((Zlength (grid_mem)) = r_pre)) (PreH16 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH17 : (0 <= i)) (PreH18 : (i < r_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= c_pre)) (PreH21 : (WallColumnsDuringRow grid_data i j occupied_data )) ,
  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
|--
  “ ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0))))) ”
).

Definition solver_partial_solve_wit_1_pure_split_goal_1 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (c_pre <= INT_MAX)) (PreH4 : (r_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (c_pre >= INT_MIN)) (PreH8 : (r_pre >= INT_MIN)) (PreH9 : (j < c_pre)) (PreH10 : (1 <= r_pre)) (PreH11 : (r_pre <= 100)) (PreH12 : (1 <= c_pre)) (PreH13 : (c_pre <= 100)) (PreH14 : (Pre r_pre c_pre grid_data )) (PreH15 : ((Zlength (grid_mem)) = r_pre)) (PreH16 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH17 : (0 <= i)) (PreH18 : (i < r_pre)) (PreH19 : (0 <= j)) (PreH20 : (j <= c_pre)) (PreH21 : (WallColumnsDuringRow grid_data i j occupied_data )) ,
  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "r" ) )) # Int  |-> r_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
|--
  “ ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0))))) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < c_pre)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i < r_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= c_pre)) (PreH13 : (WallColumnsDuringRow grid_data i j occupied_data )) ,
  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
|--
  “ (0 <= i) ” 
  &&  “ (i < r_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < c_pre) ” 
  &&  “ ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0))))) ” 
  &&  “ (j < c_pre) ” 
  &&  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= 100) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (Pre r_pre c_pre grid_data ) ” 
  &&  “ ((Zlength (grid_mem)) = r_pre) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= c_pre) ” 
  &&  “ (WallColumnsDuringRow grid_data i j occupied_data ) ”
  &&  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (cell: Z) (i: Z) (j: Z) (PreH1 : (cell = 66)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= i)) (PreH10 : (i < r_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < c_pre)) (PreH13 : (WallColumnsDuringRow grid_data i j occupied_data )) (PreH14 : (cell = (Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))) (PreH15 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (cell)))) ,
  ((((grid_pre + (i * (sizeof(CHAR) * 105))) + (j * sizeof(CHAR)))) # Char  |-> cell)
  **  (CharArray.mixed_missing_i (grid_pre + (i * (sizeof(CHAR) * 105))) j 0 105 (Znth (i) (grid_mem) ((@nil (@option Z)))) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
|--
  “ (cell = 66) ” 
  &&  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= 100) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (Pre r_pre c_pre grid_data ) ” 
  &&  “ ((Zlength (grid_mem)) = r_pre) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < c_pre) ” 
  &&  “ (WallColumnsDuringRow grid_data i j occupied_data ) ” 
  &&  “ (cell = (Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0))) ” 
  &&  “ ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (cell))) ”
  &&  (((( &( "occupied" ) ) + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "occupied" ) ) j 0 100 occupied_data )
  **  ((((grid_pre + (i * (sizeof(CHAR) * 105))) + (j * sizeof(CHAR)))) # Char  |-> cell)
  **  (CharArray.mixed_missing_i (grid_pre + (i * (sizeof(CHAR) * 105))) j 0 105 (Znth (i) (grid_mem) ((@nil (@option Z)))) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 grid_mem )
.

Definition solver_partial_solve_wit_3 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (segments: Z) (j: Z) (PreH1 : (j < c_pre)) (PreH2 : (1 <= r_pre)) (PreH3 : (r_pre <= 100)) (PreH4 : (1 <= c_pre)) (PreH5 : (c_pre <= 100)) (PreH6 : (Pre r_pre c_pre grid_data )) (PreH7 : ((Zlength (grid_mem)) = r_pre)) (PreH8 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH9 : (0 <= j)) (PreH10 : (j <= c_pre)) (PreH11 : (0 <= segments)) (PreH12 : (segments <= j)) (PreH13 : (WallColumnsAfterRows grid_data r_pre occupied_data )) (PreH14 : (SegmentCountPrefix grid_data j segments )) ,
  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
  **  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
|--
  “ (j < c_pre) ” 
  &&  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= 100) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (Pre r_pre c_pre grid_data ) ” 
  &&  “ ((Zlength (grid_mem)) = r_pre) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= c_pre) ” 
  &&  “ (0 <= segments) ” 
  &&  “ (segments <= j) ” 
  &&  “ (WallColumnsAfterRows grid_data r_pre occupied_data ) ” 
  &&  “ (SegmentCountPrefix grid_data j segments ) ”
  &&  (((( &( "occupied" ) ) + (j * sizeof(INT)))) # Int  |-> (Znth j occupied_data 0))
  **  (IntArray.missing_i ( &( "occupied" ) ) j 0 100 occupied_data )
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
.

Definition solver_partial_solve_wit_4 := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (occupied_data: (@list Z)) (segments: Z) (j: Z) (PreH1 : (j <> 0)) (PreH2 : ((Znth j occupied_data 0) <> 0)) (PreH3 : (j < c_pre)) (PreH4 : (1 <= r_pre)) (PreH5 : (r_pre <= 100)) (PreH6 : (1 <= c_pre)) (PreH7 : (c_pre <= 100)) (PreH8 : (Pre r_pre c_pre grid_data )) (PreH9 : ((Zlength (grid_mem)) = r_pre)) (PreH10 : forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH11 : (0 <= j)) (PreH12 : (j <= c_pre)) (PreH13 : (0 <= segments)) (PreH14 : (segments <= j)) (PreH15 : (WallColumnsAfterRows grid_data r_pre occupied_data )) (PreH16 : (SegmentCountPrefix grid_data j segments )) ,
  (IntArray.full ( &( "occupied" ) ) 100 occupied_data )
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
|--
  “ (j <> 0) ” 
  &&  “ ((Znth j occupied_data 0) <> 0) ” 
  &&  “ (j < c_pre) ” 
  &&  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= 100) ” 
  &&  “ (1 <= c_pre) ” 
  &&  “ (c_pre <= 100) ” 
  &&  “ (Pre r_pre c_pre grid_data ) ” 
  &&  “ ((Zlength (grid_mem)) = r_pre) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < r_pre)) -> ((((Zlength ((Znth (row) (grid_mem) ((@nil (@option Z)))))) = 105) /\ forall (col: Z) , (((0 <= col) /\ (col < c_pre)) -> ((Znth (col) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (grid_data) ((@nil Z)))) (0))))))) /\ ((Znth (c_pre) ((Znth (row) (grid_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= c_pre) ” 
  &&  “ (0 <= segments) ” 
  &&  “ (segments <= j) ” 
  &&  “ (WallColumnsAfterRows grid_data r_pre occupied_data ) ” 
  &&  “ (SegmentCountPrefix grid_data j segments ) ”
  &&  (((( &( "occupied" ) ) + ((j - 1 ) * sizeof(INT)))) # Int  |-> (Znth (j - 1 ) occupied_data 0))
  **  (IntArray.missing_i ( &( "occupied" ) ) (j - 1 ) 0 100 occupied_data )
  **  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
.

Definition solver_which_implies_wit_1 := 
(
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (i: Z) (j: Z) (PreH1 : (0 <= i)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < c_pre)) (PreH5 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))))) ,
  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
|--
  “ (0 <= i) ” 
  &&  “ (i < r_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < c_pre) ” 
  &&  “ ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0))))) ”
  &&  (CharArray.mixed_full (grid_pre + (i * (sizeof(CHAR) * 105))) 105 (Znth (i) (grid_mem) ((@nil (@option Z)))) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 grid_mem )
) \/
(
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (i: Z) (j: Z) (PreH1 : (0 <= i)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < c_pre)) (PreH5 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))))) ,
  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
|--
  (CharArray.mixed_full (grid_pre + (i * (sizeof(CHAR) * 105))) 105 (Znth (i) (grid_mem) ((@nil (@option Z)))) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 grid_mem )
).

Definition solver_which_implies_wit_1_split_goal_spatial := 
forall (c_pre: Z) (r_pre: Z) (grid_pre: Z) (grid_mem: (@list (@list (@option Z)))) (grid_data: (@list (@list Z))) (i: Z) (j: Z) (PreH1 : (0 <= i)) (PreH2 : (i < r_pre)) (PreH3 : (0 <= j)) (PreH4 : (j < c_pre)) (PreH5 : ((Znth (j) ((Znth (i) (grid_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j) ((Znth (i) (grid_data) ((@nil Z)))) (0)))))) ,
  (CharArray2.mixed_full grid_pre r_pre 105 grid_mem )
|--
  (CharArray.mixed_full (grid_pre + (i * (sizeof(CHAR) * 105))) 105 (Znth (i) (grid_mem) ((@nil (@option Z)))) )
  **  (CharArray2.mixed_missing_i grid_pre i 0 r_pre 105 grid_mem )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1.
Axiom proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2.
Axiom proof_of_solver_entail_wit_8_3 : solver_entail_wit_8_3.
Axiom proof_of_solver_entail_wit_8_4 : solver_entail_wit_8_4.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.

End VC_Correct.
