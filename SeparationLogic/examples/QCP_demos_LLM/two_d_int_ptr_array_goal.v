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
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.

(*----- Function max_fill -----*)

Definition max_fill_safety_wit_1 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (0 <= grid_rows_pre)) (PreH2 : (grid_rows_pre <= 100)) (PreH3 : (0 <= grid_cols_pre)) (PreH4 : (grid_cols_pre <= 100)) (PreH5 : (1 <= capacity_pre)) (PreH6 : (capacity_pre <= 10)) (PreH7 : ((Zlength (rows)) = grid_rows_pre)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < grid_rows_pre)) -> ((Zlength ((Znth i rows __default__List_Z))) = grid_cols_pre))) (PreH9 : forall (i_2: Z) , forall (j: Z) , (((((0 <= i_2) /\ (i_2 < grid_rows_pre)) /\ (0 <= j)) /\ (j < grid_cols_pre)) -> ((0 <= (Znth j (Znth i_2 rows __default__List_Z) 0)) /\ ((Znth j (Znth i_2 rows __default__List_Z) 0) <= 1)))) ,
  ((( &( "out" ) )) # Int  |->_)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition max_fill_safety_wit_2 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (0 <= grid_rows_pre)) (PreH2 : (grid_rows_pre <= 100)) (PreH3 : (0 <= grid_cols_pre)) (PreH4 : (grid_cols_pre <= 100)) (PreH5 : (1 <= capacity_pre)) (PreH6 : (capacity_pre <= 10)) (PreH7 : ((Zlength (rows)) = grid_rows_pre)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < grid_rows_pre)) -> ((Zlength ((Znth i rows __default__List_Z))) = grid_cols_pre))) (PreH9 : forall (i_2: Z) , forall (j: Z) , (((((0 <= i_2) /\ (i_2 < grid_rows_pre)) /\ (0 <= j)) /\ (j < grid_cols_pre)) -> ((0 <= (Znth j (Znth i_2 rows __default__List_Z) 0)) /\ ((Znth j (Znth i_2 rows __default__List_Z) 0) <= 1)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Int  |-> 0)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition max_fill_safety_wit_3 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (i: Z)  __default__List_Z (PreH1 : (i < grid_rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= grid_rows_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : ((Zlength (rows)) = grid_rows_pre)) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH12 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) (PreH13 : (0 <= out)) (PreH14 : (out <= (i * grid_cols_pre ))) ,
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition max_fill_safety_wit_4 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < grid_rows_pre)) (PreH3 : (0 <= grid_rows_pre)) (PreH4 : (grid_rows_pre <= 100)) (PreH5 : (0 <= grid_cols_pre)) (PreH6 : (grid_cols_pre <= 100)) (PreH7 : (1 <= capacity_pre)) (PreH8 : (capacity_pre <= 10)) (PreH9 : (0 <= i)) (PreH10 : (i < grid_rows_pre)) (PreH11 : (0 <= sum)) (PreH12 : (sum <= grid_cols_pre)) (PreH13 : (0 <= out)) (PreH14 : (out <= (i * grid_cols_pre ))) (PreH15 : ((Zlength (rows)) = grid_rows_pre)) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH17 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) (PreH18 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre)) (PreH19 : (0 <= out)) (PreH20 : (out <= (i * grid_cols_pre ))) (PreH21 : (sum = 0)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (IntPtrArray2.missing_i grid_pre grid_rows_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition max_fill_safety_wit_5 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (sum: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < grid_cols_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= grid_cols_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : (0 <= i)) (PreH11 : (i < grid_rows_pre)) (PreH12 : (0 <= sum)) (PreH13 : (sum <= grid_cols_pre)) (PreH14 : (0 <= out)) (PreH15 : (out <= (i * grid_cols_pre ))) (PreH16 : ((Zlength (rows)) = grid_rows_pre)) (PreH17 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH18 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < grid_rows_pre)) (PreH22 : (0 <= sum)) (PreH23 : (sum <= j)) (PreH24 : (0 <= out)) (PreH25 : (out <= (i * grid_cols_pre ))) ,
  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (Znth j (Znth (i) (rows) ((@nil Z))) 0) ))
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (IntPtrArray2.missing_i grid_pre grid_rows_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition max_fill_safety_wit_6 := 
(
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (sum: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < grid_cols_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= grid_cols_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : (0 <= i)) (PreH11 : (i < grid_rows_pre)) (PreH12 : (0 <= sum)) (PreH13 : (sum <= grid_cols_pre)) (PreH14 : (0 <= out)) (PreH15 : (out <= (i * grid_cols_pre ))) (PreH16 : ((Zlength (rows)) = grid_rows_pre)) (PreH17 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH18 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < grid_rows_pre)) (PreH22 : (0 <= sum)) (PreH23 : (sum <= j)) (PreH24 : (0 <= out)) (PreH25 : (out <= (i * grid_cols_pre ))) ,
  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (IntPtrArray2.missing_i grid_pre grid_rows_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((sum + (Znth j (Znth (i) (rows) ((@nil Z))) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (Znth j (Znth (i) (rows) ((@nil Z))) 0) )) ”
) \/
(
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (sum: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < grid_cols_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= grid_cols_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : (0 <= i)) (PreH11 : (i < grid_rows_pre)) (PreH12 : (0 <= sum)) (PreH13 : (sum <= grid_cols_pre)) (PreH14 : (0 <= out)) (PreH15 : (out <= (i * grid_cols_pre ))) (PreH16 : ((Zlength (rows)) = grid_rows_pre)) (PreH17 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH18 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < grid_rows_pre)) (PreH22 : (0 <= sum)) (PreH23 : (sum <= j)) (PreH24 : (0 <= out)) (PreH25 : (out <= (i * grid_cols_pre ))) ,
  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (IntPtrArray2.missing_i grid_pre grid_rows_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((sum + (Znth j (Znth (i) (rows) ((@nil Z))) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (Znth j (Znth (i) (rows) ((@nil Z))) 0) )) ”
).

Definition max_fill_safety_wit_6_split_goal_1 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (sum: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < grid_cols_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= grid_cols_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : (0 <= i)) (PreH11 : (i < grid_rows_pre)) (PreH12 : (0 <= sum)) (PreH13 : (sum <= grid_cols_pre)) (PreH14 : (0 <= out)) (PreH15 : (out <= (i * grid_cols_pre ))) (PreH16 : ((Zlength (rows)) = grid_rows_pre)) (PreH17 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH18 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < grid_rows_pre)) (PreH22 : (0 <= sum)) (PreH23 : (sum <= j)) (PreH24 : (0 <= out)) (PreH25 : (out <= (i * grid_cols_pre ))) ,
  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (IntPtrArray2.missing_i grid_pre grid_rows_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((sum + (Znth j (Znth (i) (rows) ((@nil Z))) 0) ) <= INT_MAX) ”
.

Definition max_fill_safety_wit_6_split_goal_2 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (sum: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < grid_cols_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= grid_cols_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : (0 <= i)) (PreH11 : (i < grid_rows_pre)) (PreH12 : (0 <= sum)) (PreH13 : (sum <= grid_cols_pre)) (PreH14 : (0 <= out)) (PreH15 : (out <= (i * grid_cols_pre ))) (PreH16 : ((Zlength (rows)) = grid_rows_pre)) (PreH17 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH18 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < grid_rows_pre)) (PreH22 : (0 <= sum)) (PreH23 : (sum <= j)) (PreH24 : (0 <= out)) (PreH25 : (out <= (i * grid_cols_pre ))) ,
  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  (IntPtrArray2.missing_i grid_pre grid_rows_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((INT_MIN) <= (sum + (Znth j (Znth (i) (rows) ((@nil Z))) 0) )) ”
.

Definition max_fill_safety_wit_7 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (0 <= grid_rows_pre)) (PreH2 : (grid_rows_pre <= 100)) (PreH3 : (0 <= grid_cols_pre)) (PreH4 : (grid_cols_pre <= 100)) (PreH5 : (1 <= capacity_pre)) (PreH6 : (capacity_pre <= 10)) (PreH7 : (0 <= i)) (PreH8 : (i < grid_rows_pre)) (PreH9 : (0 <= sum)) (PreH10 : (sum <= grid_cols_pre)) (PreH11 : (0 <= out)) (PreH12 : (out <= (i * grid_cols_pre ))) (PreH13 : ((Zlength (rows)) = grid_rows_pre)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH15 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition max_fill_safety_wit_8 := 
(
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum > 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ ((out + (((sum - 1 ) ÷ capacity_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out + (((sum - 1 ) ÷ capacity_pre ) + 1 ) )) ”
) \/
(
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum > 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ ((out + (((sum - 1 ) ÷ capacity_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out + (((sum - 1 ) ÷ capacity_pre ) + 1 ) )) ”
).

Definition max_fill_safety_wit_8_split_goal_1 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum > 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ ((out + (((sum - 1 ) ÷ capacity_pre ) + 1 ) ) <= INT_MAX) ”
.

Definition max_fill_safety_wit_8_split_goal_2 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum > 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ ((INT_MIN) <= (out + (((sum - 1 ) ÷ capacity_pre ) + 1 ) )) ”
.

Definition max_fill_safety_wit_9 := 
(
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum > 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ ((((sum - 1 ) ÷ capacity_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((sum - 1 ) ÷ capacity_pre ) + 1 )) ”
) \/
(
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum > 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ ((((sum - 1 ) ÷ capacity_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((sum - 1 ) ÷ capacity_pre ) + 1 )) ”
).

Definition max_fill_safety_wit_9_split_goal_1 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum > 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ ((((sum - 1 ) ÷ capacity_pre ) + 1 ) <= INT_MAX) ”
.

Definition max_fill_safety_wit_9_split_goal_2 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum > 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ ((INT_MIN) <= (((sum - 1 ) ÷ capacity_pre ) + 1 )) ”
.

Definition max_fill_safety_wit_10 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum > 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ (((sum - 1 ) <> (INT_MIN)) \/ (capacity_pre <> (-1))) ” 
  &&  “ (capacity_pre <> 0) ”
.

Definition max_fill_safety_wit_11 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum > 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ ((sum - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum - 1 )) ”
.

Definition max_fill_safety_wit_12 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum > 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition max_fill_safety_wit_13 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum > 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition max_fill_safety_wit_14 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum > 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> (out + (((sum - 1 ) ÷ capacity_pre ) + 1 ) ))
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition max_fill_safety_wit_15 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum <= 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "grid_rows" ) )) # Int  |-> grid_rows_pre)
  **  ((( &( "grid_cols" ) )) # Int  |-> grid_cols_pre)
  **  ((( &( "grid" ) )) # Ptr  |-> grid_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition max_fill_entail_wit_1 := 
(
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (0 <= grid_rows_pre)) (PreH2 : (grid_rows_pre <= 100)) (PreH3 : (0 <= grid_cols_pre)) (PreH4 : (grid_cols_pre <= 100)) (PreH5 : (1 <= capacity_pre)) (PreH6 : (capacity_pre <= 10)) (PreH7 : ((Zlength (rows)) = grid_rows_pre)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < grid_rows_pre)) -> ((Zlength ((Znth i rows __default__List_Z))) = grid_cols_pre))) (PreH9 : forall (i_2: Z) , forall (j: Z) , (((((0 <= i_2) /\ (i_2 < grid_rows_pre)) /\ (0 <= j)) /\ (j < grid_cols_pre)) -> ((0 <= (Znth j (Znth i_2 rows __default__List_Z) 0)) /\ ((Znth j (Znth i_2 rows __default__List_Z) 0) <= 1)))) ,
  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= grid_rows_pre) ” 
  &&  “ (0 <= grid_rows_pre) ” 
  &&  “ (grid_rows_pre <= 100) ” 
  &&  “ (0 <= grid_cols_pre) ” 
  &&  “ (grid_cols_pre <= 100) ” 
  &&  “ (1 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 10) ” 
  &&  “ ((Zlength (rows)) = grid_rows_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (0 * grid_cols_pre )) ”
  &&  (IntPtrArray2.full grid_pre grid_rows_pre rows )
) \/
(
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (0 <= grid_rows_pre)) (PreH2 : (grid_rows_pre <= 100)) (PreH3 : (0 <= grid_cols_pre)) (PreH4 : (grid_cols_pre <= 100)) (PreH5 : (1 <= capacity_pre)) (PreH6 : (capacity_pre <= 10)) (PreH7 : ((Zlength (rows)) = grid_rows_pre)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < grid_rows_pre)) -> ((Zlength ((Znth i rows __default__List_Z))) = grid_cols_pre))) (PreH9 : forall (i_2: Z) , forall (j: Z) , (((((0 <= i_2) /\ (i_2 < grid_rows_pre)) /\ (0 <= j)) /\ (j < grid_cols_pre)) -> ((0 <= (Znth j (Znth i_2 rows __default__List_Z) 0)) /\ ((Znth j (Znth i_2 rows __default__List_Z) 0) <= 1)))) ,
  TT && emp 
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1))) ”
  &&  emp
).

Definition max_fill_entail_wit_1_split_goal_1 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (rows: (@list (@list Z)))  __default__List_Z (PreH1 : (0 <= grid_rows_pre)) (PreH2 : (grid_rows_pre <= 100)) (PreH3 : (0 <= grid_cols_pre)) (PreH4 : (grid_cols_pre <= 100)) (PreH5 : (1 <= capacity_pre)) (PreH6 : (capacity_pre <= 10)) (PreH7 : ((Zlength (rows)) = grid_rows_pre)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < grid_rows_pre)) -> ((Zlength ((Znth i rows __default__List_Z))) = grid_cols_pre))) (PreH9 : forall (i_2: Z) , forall (j: Z) , (((((0 <= i_2) /\ (i_2 < grid_rows_pre)) /\ (0 <= j)) /\ (j < grid_cols_pre)) -> ((0 <= (Znth j (Znth i_2 rows __default__List_Z) 0)) /\ ((Znth j (Znth i_2 rows __default__List_Z) 0) <= 1)))) ,
  forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))
.

Definition max_fill_entail_wit_2 := 
(
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (i: Z)  __default__List_Z (PreH1 : (i < grid_rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= grid_rows_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : ((Zlength (rows)) = grid_rows_pre)) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH12 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) (PreH13 : (0 <= out)) (PreH14 : (out <= (i * grid_cols_pre ))) ,
  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < grid_rows_pre) ” 
  &&  “ (0 <= grid_rows_pre) ” 
  &&  “ (grid_rows_pre <= 100) ” 
  &&  “ (0 <= grid_cols_pre) ” 
  &&  “ (grid_cols_pre <= 100) ” 
  &&  “ (1 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < grid_rows_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= grid_cols_pre) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out <= (i * grid_cols_pre )) ” 
  &&  “ ((Zlength (rows)) = grid_rows_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1))) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out <= (i * grid_cols_pre )) ” 
  &&  “ (0 = 0) ”
  &&  (IntPtrArray2.missing_i grid_pre grid_rows_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
) \/
(
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (rows: (@list (@list Z))) (out: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (i < grid_rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= grid_rows_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : ((Zlength (rows)) = grid_rows_pre)) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH12 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) (PreH13 : (0 <= out)) (PreH14 : (out <= (i * grid_cols_pre ))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1))) ”
  &&  (IntArray.full row_ptr_2 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
).

Definition max_fill_entail_wit_2_split_goal_1 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (rows: (@list (@list Z))) (out: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (i < grid_rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= grid_rows_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : ((Zlength (rows)) = grid_rows_pre)) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH12 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) (PreH13 : (0 <= out)) (PreH14 : (out <= (i * grid_cols_pre ))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre) ”
.

Definition max_fill_entail_wit_2_split_goal_2 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (rows: (@list (@list Z))) (out: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (i < grid_rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= grid_rows_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : ((Zlength (rows)) = grid_rows_pre)) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH12 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) (PreH13 : (0 <= out)) (PreH14 : (out <= (i * grid_cols_pre ))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1))) ”
.

Definition max_fill_entail_wit_2_split_goal_spatial := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (rows: (@list (@list Z))) (out: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (i < grid_rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= grid_rows_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : ((Zlength (rows)) = grid_rows_pre)) (PreH11 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH12 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) (PreH13 : (0 <= out)) (PreH14 : (out <= (i * grid_cols_pre ))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  (IntArray.full row_ptr_2 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
.

Definition max_fill_entail_wit_3 := 
(
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr_2: Z) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < grid_rows_pre)) (PreH3 : (0 <= grid_rows_pre)) (PreH4 : (grid_rows_pre <= 100)) (PreH5 : (0 <= grid_cols_pre)) (PreH6 : (grid_cols_pre <= 100)) (PreH7 : (1 <= capacity_pre)) (PreH8 : (capacity_pre <= 10)) (PreH9 : (0 <= i)) (PreH10 : (i < grid_rows_pre)) (PreH11 : (0 <= sum)) (PreH12 : (sum <= grid_cols_pre)) (PreH13 : (0 <= out)) (PreH14 : (out <= (i * grid_cols_pre ))) (PreH15 : ((Zlength (rows)) = grid_rows_pre)) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) (PreH18 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre)) (PreH19 : (0 <= out)) (PreH20 : (out <= (i * grid_cols_pre ))) (PreH21 : (sum = 0)) ,
  (IntPtrArray2.missing_i grid_pre grid_rows_pre i row_ptr_2 rows )
  **  (((grid_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr_2)
  **  (IntArray.full row_ptr_2 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  EX (row_ptr: Z) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= grid_cols_pre) ” 
  &&  “ (0 <= grid_rows_pre) ” 
  &&  “ (grid_rows_pre <= 100) ” 
  &&  “ (0 <= grid_cols_pre) ” 
  &&  “ (grid_cols_pre <= 100) ” 
  &&  “ (1 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < grid_rows_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= grid_cols_pre) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out <= (i * grid_cols_pre )) ” 
  &&  “ ((Zlength (rows)) = grid_rows_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1))) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < grid_rows_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= 0) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out <= (i * grid_cols_pre )) ”
  &&  (IntPtrArray2.missing_i grid_pre grid_rows_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
) \/
(
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < grid_rows_pre)) (PreH3 : (0 <= grid_rows_pre)) (PreH4 : (grid_rows_pre <= 100)) (PreH5 : (0 <= grid_cols_pre)) (PreH6 : (grid_cols_pre <= 100)) (PreH7 : (1 <= capacity_pre)) (PreH8 : (capacity_pre <= 10)) (PreH9 : (0 <= i)) (PreH10 : (i < grid_rows_pre)) (PreH11 : (0 <= sum)) (PreH12 : (sum <= grid_cols_pre)) (PreH13 : (0 <= out)) (PreH14 : (out <= (i * grid_cols_pre ))) (PreH15 : ((Zlength (rows)) = grid_rows_pre)) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) (PreH18 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre)) (PreH19 : (0 <= out)) (PreH20 : (out <= (i * grid_cols_pre ))) (PreH21 : (sum = 0)) ,
  TT && emp 
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1))) ”
  &&  emp
).

Definition max_fill_entail_wit_3_split_goal_1 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (0 <= i)) (PreH2 : (i < grid_rows_pre)) (PreH3 : (0 <= grid_rows_pre)) (PreH4 : (grid_rows_pre <= 100)) (PreH5 : (0 <= grid_cols_pre)) (PreH6 : (grid_cols_pre <= 100)) (PreH7 : (1 <= capacity_pre)) (PreH8 : (capacity_pre <= 10)) (PreH9 : (0 <= i)) (PreH10 : (i < grid_rows_pre)) (PreH11 : (0 <= sum)) (PreH12 : (sum <= grid_cols_pre)) (PreH13 : (0 <= out)) (PreH14 : (out <= (i * grid_cols_pre ))) (PreH15 : ((Zlength (rows)) = grid_rows_pre)) (PreH16 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH17 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) (PreH18 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre)) (PreH19 : (0 <= out)) (PreH20 : (out <= (i * grid_cols_pre ))) (PreH21 : (sum = 0)) ,
  forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))
.

Definition max_fill_entail_wit_4 := 
(
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr_2: Z) (out: Z) (sum: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < grid_cols_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= grid_cols_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : (0 <= i)) (PreH11 : (i < grid_rows_pre)) (PreH12 : (0 <= sum)) (PreH13 : (sum <= grid_cols_pre)) (PreH14 : (0 <= out)) (PreH15 : (out <= (i * grid_cols_pre ))) (PreH16 : ((Zlength (rows)) = grid_rows_pre)) (PreH17 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH18 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < grid_rows_pre)) (PreH22 : (0 <= sum)) (PreH23 : (sum <= j)) (PreH24 : (0 <= out)) (PreH25 : (out <= (i * grid_cols_pre ))) ,
  (IntArray.full row_ptr_2 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntPtrArray2.missing_i grid_pre grid_rows_pre i row_ptr_2 rows )
  **  (((grid_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr_2)
|--
  EX (row_ptr: Z) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= grid_cols_pre) ” 
  &&  “ (0 <= grid_rows_pre) ” 
  &&  “ (grid_rows_pre <= 100) ” 
  &&  “ (0 <= grid_cols_pre) ” 
  &&  “ (grid_cols_pre <= 100) ” 
  &&  “ (1 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < grid_rows_pre) ” 
  &&  “ (0 <= (sum + (Znth j (Znth (i) (rows) ((@nil Z))) 0) )) ” 
  &&  “ ((sum + (Znth j (Znth (i) (rows) ((@nil Z))) 0) ) <= grid_cols_pre) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out <= (i * grid_cols_pre )) ” 
  &&  “ ((Zlength (rows)) = grid_rows_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1))) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < grid_rows_pre) ” 
  &&  “ (0 <= (sum + (Znth j (Znth (i) (rows) ((@nil Z))) 0) )) ” 
  &&  “ ((sum + (Znth j (Znth (i) (rows) ((@nil Z))) 0) ) <= (j + 1 )) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out <= (i * grid_cols_pre )) ”
  &&  (IntPtrArray2.missing_i grid_pre grid_rows_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
) \/
(
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (rows: (@list (@list Z))) (out: Z) (sum: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < grid_cols_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= grid_cols_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : (0 <= i)) (PreH11 : (i < grid_rows_pre)) (PreH12 : (0 <= sum)) (PreH13 : (sum <= grid_cols_pre)) (PreH14 : (0 <= out)) (PreH15 : (out <= (i * grid_cols_pre ))) (PreH16 : ((Zlength (rows)) = grid_rows_pre)) (PreH17 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH18 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < grid_rows_pre)) (PreH22 : (0 <= sum)) (PreH23 : (sum <= j)) (PreH24 : (0 <= out)) (PreH25 : (out <= (i * grid_cols_pre ))) ,
  TT && emp 
|--
  “ ((sum + (Znth j (Znth (i) (rows) ((@nil Z))) 0) ) <= (j + 1 )) ” 
  &&  “ (0 <= (sum + (Znth j (Znth (i) (rows) ((@nil Z))) 0) )) ” 
  &&  “ ((sum + (Znth j (Znth (i) (rows) ((@nil Z))) 0) ) <= grid_cols_pre) ” 
  &&  “ (0 <= (sum + (Znth j (Znth (i) (rows) ((@nil Z))) 0) )) ”
  &&  emp
).

Definition max_fill_entail_wit_4_split_goal_1 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (rows: (@list (@list Z))) (out: Z) (sum: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < grid_cols_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= grid_cols_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : (0 <= i)) (PreH11 : (i < grid_rows_pre)) (PreH12 : (0 <= sum)) (PreH13 : (sum <= grid_cols_pre)) (PreH14 : (0 <= out)) (PreH15 : (out <= (i * grid_cols_pre ))) (PreH16 : ((Zlength (rows)) = grid_rows_pre)) (PreH17 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH18 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < grid_rows_pre)) (PreH22 : (0 <= sum)) (PreH23 : (sum <= j)) (PreH24 : (0 <= out)) (PreH25 : (out <= (i * grid_cols_pre ))) ,
  ((sum + (Znth j (Znth (i) (rows) ((@nil Z))) 0) ) <= (j + 1 ))
.

Definition max_fill_entail_wit_4_split_goal_2 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (rows: (@list (@list Z))) (out: Z) (sum: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < grid_cols_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= grid_cols_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : (0 <= i)) (PreH11 : (i < grid_rows_pre)) (PreH12 : (0 <= sum)) (PreH13 : (sum <= grid_cols_pre)) (PreH14 : (0 <= out)) (PreH15 : (out <= (i * grid_cols_pre ))) (PreH16 : ((Zlength (rows)) = grid_rows_pre)) (PreH17 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH18 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < grid_rows_pre)) (PreH22 : (0 <= sum)) (PreH23 : (sum <= j)) (PreH24 : (0 <= out)) (PreH25 : (out <= (i * grid_cols_pre ))) ,
  (0 <= (sum + (Znth j (Znth (i) (rows) ((@nil Z))) 0) ))
.

Definition max_fill_entail_wit_4_split_goal_3 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (rows: (@list (@list Z))) (out: Z) (sum: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < grid_cols_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= grid_cols_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : (0 <= i)) (PreH11 : (i < grid_rows_pre)) (PreH12 : (0 <= sum)) (PreH13 : (sum <= grid_cols_pre)) (PreH14 : (0 <= out)) (PreH15 : (out <= (i * grid_cols_pre ))) (PreH16 : ((Zlength (rows)) = grid_rows_pre)) (PreH17 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH18 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < grid_rows_pre)) (PreH22 : (0 <= sum)) (PreH23 : (sum <= j)) (PreH24 : (0 <= out)) (PreH25 : (out <= (i * grid_cols_pre ))) ,
  ((sum + (Znth j (Znth (i) (rows) ((@nil Z))) 0) ) <= grid_cols_pre)
.

Definition max_fill_entail_wit_4_split_goal_4 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (rows: (@list (@list Z))) (out: Z) (sum: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < grid_cols_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= grid_cols_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : (0 <= i)) (PreH11 : (i < grid_rows_pre)) (PreH12 : (0 <= sum)) (PreH13 : (sum <= grid_cols_pre)) (PreH14 : (0 <= out)) (PreH15 : (out <= (i * grid_cols_pre ))) (PreH16 : ((Zlength (rows)) = grid_rows_pre)) (PreH17 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH18 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < grid_rows_pre)) (PreH22 : (0 <= sum)) (PreH23 : (sum <= j)) (PreH24 : (0 <= out)) (PreH25 : (out <= (i * grid_cols_pre ))) ,
  (0 <= (sum + (Znth j (Znth (i) (rows) ((@nil Z))) 0) ))
.

Definition max_fill_entail_wit_5 := 
(
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (sum: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j >= grid_cols_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= grid_cols_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : (0 <= i)) (PreH11 : (i < grid_rows_pre)) (PreH12 : (0 <= sum)) (PreH13 : (sum <= grid_cols_pre)) (PreH14 : (0 <= out)) (PreH15 : (out <= (i * grid_cols_pre ))) (PreH16 : ((Zlength (rows)) = grid_rows_pre)) (PreH17 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH18 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < grid_rows_pre)) (PreH22 : (0 <= sum)) (PreH23 : (sum <= j)) (PreH24 : (0 <= out)) (PreH25 : (out <= (i * grid_cols_pre ))) ,
  (IntPtrArray2.missing_i grid_pre grid_rows_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (0 <= grid_rows_pre) ” 
  &&  “ (grid_rows_pre <= 100) ” 
  &&  “ (0 <= grid_cols_pre) ” 
  &&  “ (grid_cols_pre <= 100) ” 
  &&  “ (1 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < grid_rows_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= grid_cols_pre) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out <= (i * grid_cols_pre )) ” 
  &&  “ ((Zlength (rows)) = grid_rows_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1))) ”
  &&  (IntPtrArray2.full grid_pre grid_rows_pre rows )
) \/
(
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (sum: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j >= grid_cols_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= grid_cols_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : (0 <= i)) (PreH11 : (i < grid_rows_pre)) (PreH12 : (0 <= sum)) (PreH13 : (sum <= grid_cols_pre)) (PreH14 : (0 <= out)) (PreH15 : (out <= (i * grid_cols_pre ))) (PreH16 : ((Zlength (rows)) = grid_rows_pre)) (PreH17 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH18 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < grid_rows_pre)) (PreH22 : (0 <= sum)) (PreH23 : (sum <= j)) (PreH24 : (0 <= out)) (PreH25 : (out <= (i * grid_cols_pre ))) ,
  (IntPtrArray2.missing_i grid_pre grid_rows_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1))) ”
  &&  (IntPtrArray2.full grid_pre grid_rows_pre rows )
).

Definition max_fill_entail_wit_5_split_goal_1 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (sum: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j >= grid_cols_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= grid_cols_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : (0 <= i)) (PreH11 : (i < grid_rows_pre)) (PreH12 : (0 <= sum)) (PreH13 : (sum <= grid_cols_pre)) (PreH14 : (0 <= out)) (PreH15 : (out <= (i * grid_cols_pre ))) (PreH16 : ((Zlength (rows)) = grid_rows_pre)) (PreH17 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH18 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < grid_rows_pre)) (PreH22 : (0 <= sum)) (PreH23 : (sum <= j)) (PreH24 : (0 <= out)) (PreH25 : (out <= (i * grid_cols_pre ))) ,
  (IntPtrArray2.missing_i grid_pre grid_rows_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1))) ”
.

Definition max_fill_entail_wit_5_split_goal_spatial := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (sum: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j >= grid_cols_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= grid_cols_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : (0 <= i)) (PreH11 : (i < grid_rows_pre)) (PreH12 : (0 <= sum)) (PreH13 : (sum <= grid_cols_pre)) (PreH14 : (0 <= out)) (PreH15 : (out <= (i * grid_cols_pre ))) (PreH16 : ((Zlength (rows)) = grid_rows_pre)) (PreH17 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH18 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < grid_rows_pre)) (PreH22 : (0 <= sum)) (PreH23 : (sum <= j)) (PreH24 : (0 <= out)) (PreH25 : (out <= (i * grid_cols_pre ))) ,
  (IntPtrArray2.missing_i grid_pre grid_rows_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  (IntPtrArray2.full grid_pre grid_rows_pre rows )
.

Definition max_fill_entail_wit_6_1 := 
(
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum > 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) ,
  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= grid_rows_pre) ” 
  &&  “ (0 <= grid_rows_pre) ” 
  &&  “ (grid_rows_pre <= 100) ” 
  &&  “ (0 <= grid_cols_pre) ” 
  &&  “ (grid_cols_pre <= 100) ” 
  &&  “ (1 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 10) ” 
  &&  “ ((Zlength (rows)) = grid_rows_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1))) ” 
  &&  “ (0 <= (out + (((sum - 1 ) ÷ capacity_pre ) + 1 ) )) ” 
  &&  “ ((out + (((sum - 1 ) ÷ capacity_pre ) + 1 ) ) <= ((i + 1 ) * grid_cols_pre )) ”
  &&  (IntPtrArray2.full grid_pre grid_rows_pre rows )
) \/
(
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum > 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) ,
  TT && emp 
|--
  “ ((out + (((sum - 1 ) ÷ capacity_pre ) + 1 ) ) <= ((i + 1 ) * grid_cols_pre )) ” 
  &&  “ (0 <= (out + (((sum - 1 ) ÷ capacity_pre ) + 1 ) )) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1))) ”
  &&  emp
).

Definition max_fill_entail_wit_6_1_split_goal_1 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum > 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) ,
  ((out + (((sum - 1 ) ÷ capacity_pre ) + 1 ) ) <= ((i + 1 ) * grid_cols_pre ))
.

Definition max_fill_entail_wit_6_1_split_goal_2 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum > 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) ,
  (0 <= (out + (((sum - 1 ) ÷ capacity_pre ) + 1 ) ))
.

Definition max_fill_entail_wit_6_1_split_goal_3 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum > 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) ,
  forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))
.

Definition max_fill_entail_wit_6_2 := 
(
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum <= 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) ,
  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= grid_rows_pre) ” 
  &&  “ (0 <= grid_rows_pre) ” 
  &&  “ (grid_rows_pre <= 100) ” 
  &&  “ (0 <= grid_cols_pre) ” 
  &&  “ (grid_cols_pre <= 100) ” 
  &&  “ (1 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 10) ” 
  &&  “ ((Zlength (rows)) = grid_rows_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1))) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out <= ((i + 1 ) * grid_cols_pre )) ”
  &&  (IntPtrArray2.full grid_pre grid_rows_pre rows )
) \/
(
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum <= 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) ,
  TT && emp 
|--
  “ (out <= ((i + 1 ) * grid_cols_pre )) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1))) ”
  &&  emp
).

Definition max_fill_entail_wit_6_2_split_goal_1 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum <= 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) ,
  (out <= ((i + 1 ) * grid_cols_pre ))
.

Definition max_fill_entail_wit_6_2_split_goal_2 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (rows: (@list (@list Z))) (i: Z) (sum: Z) (out: Z)  __default__List_Z (PreH1 : (sum <= 0)) (PreH2 : (0 <= grid_rows_pre)) (PreH3 : (grid_rows_pre <= 100)) (PreH4 : (0 <= grid_cols_pre)) (PreH5 : (grid_cols_pre <= 100)) (PreH6 : (1 <= capacity_pre)) (PreH7 : (capacity_pre <= 10)) (PreH8 : (0 <= i)) (PreH9 : (i < grid_rows_pre)) (PreH10 : (0 <= sum)) (PreH11 : (sum <= grid_cols_pre)) (PreH12 : (0 <= out)) (PreH13 : (out <= (i * grid_cols_pre ))) (PreH14 : ((Zlength (rows)) = grid_rows_pre)) (PreH15 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < grid_rows_pre)) -> ((Zlength ((Znth r_3 rows __default__List_Z))) = grid_cols_pre))) (PreH16 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < grid_rows_pre)) /\ (0 <= c_2)) /\ (c_2 < grid_cols_pre)) -> ((0 <= (Znth c_2 (Znth r_4 rows __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 rows __default__List_Z) 0) <= 1)))) ,
  forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))
.

Definition max_fill_return_wit_1 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (out: Z) (i: Z)  __default__List_Z (PreH1 : (i >= grid_rows_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= grid_rows_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : ((Zlength (rows)) = grid_rows_pre)) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH12 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) (PreH13 : (0 <= out)) (PreH14 : (out <= (i * grid_cols_pre ))) ,
  (IntPtrArray2.full grid_pre grid_rows_pre rows )
|--
  (IntPtrArray2.full grid_pre grid_rows_pre rows )
.

Definition max_fill_partial_solve_wit_1 := 
forall (capacity_pre: Z) (grid_cols_pre: Z) (grid_rows_pre: Z) (grid_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (out: Z) (sum: Z) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < grid_cols_pre)) (PreH2 : (0 <= j)) (PreH3 : (j <= grid_cols_pre)) (PreH4 : (0 <= grid_rows_pre)) (PreH5 : (grid_rows_pre <= 100)) (PreH6 : (0 <= grid_cols_pre)) (PreH7 : (grid_cols_pre <= 100)) (PreH8 : (1 <= capacity_pre)) (PreH9 : (capacity_pre <= 10)) (PreH10 : (0 <= i)) (PreH11 : (i < grid_rows_pre)) (PreH12 : (0 <= sum)) (PreH13 : (sum <= grid_cols_pre)) (PreH14 : (0 <= out)) (PreH15 : (out <= (i * grid_cols_pre ))) (PreH16 : ((Zlength (rows)) = grid_rows_pre)) (PreH17 : forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre))) (PreH18 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1)))) (PreH19 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre)) (PreH20 : (0 <= i)) (PreH21 : (i < grid_rows_pre)) (PreH22 : (0 <= sum)) (PreH23 : (sum <= j)) (PreH24 : (0 <= out)) (PreH25 : (out <= (i * grid_cols_pre ))) ,
  (IntPtrArray2.missing_i grid_pre grid_rows_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  “ (j < grid_cols_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= grid_cols_pre) ” 
  &&  “ (0 <= grid_rows_pre) ” 
  &&  “ (grid_rows_pre <= 100) ” 
  &&  “ (0 <= grid_cols_pre) ” 
  &&  “ (grid_cols_pre <= 100) ” 
  &&  “ (1 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 10) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < grid_rows_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= grid_cols_pre) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out <= (i * grid_cols_pre )) ” 
  &&  “ ((Zlength (rows)) = grid_rows_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < grid_rows_pre)) -> ((Zlength ((Znth r rows __default__List_Z))) = grid_cols_pre)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < grid_rows_pre)) /\ (0 <= c)) /\ (c < grid_cols_pre)) -> ((0 <= (Znth c (Znth r_2 rows __default__List_Z) 0)) /\ ((Znth c (Znth r_2 rows __default__List_Z) 0) <= 1))) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = grid_cols_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < grid_rows_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= j) ” 
  &&  “ (0 <= out) ” 
  &&  “ (out <= (i * grid_cols_pre )) ”
  &&  (((row_ptr + (j * sizeof(INT)))) # Int  |-> (Znth j (Znth (i) (rows) ((@nil Z))) 0))
  **  (IntArray.missing_i row_ptr j 0 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntPtrArray2.missing_i grid_pre grid_rows_pre i row_ptr rows )
  **  (((grid_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
.

Module Type VC_Correct.

Include int_ptr_array2_Strategy_Correct.
Include int_array_Strategy_Correct.

Axiom proof_of_max_fill_safety_wit_1 : max_fill_safety_wit_1.
Axiom proof_of_max_fill_safety_wit_2 : max_fill_safety_wit_2.
Axiom proof_of_max_fill_safety_wit_3 : max_fill_safety_wit_3.
Axiom proof_of_max_fill_safety_wit_4 : max_fill_safety_wit_4.
Axiom proof_of_max_fill_safety_wit_5 : max_fill_safety_wit_5.
Axiom proof_of_max_fill_safety_wit_6 : max_fill_safety_wit_6.
Axiom proof_of_max_fill_safety_wit_7 : max_fill_safety_wit_7.
Axiom proof_of_max_fill_safety_wit_8 : max_fill_safety_wit_8.
Axiom proof_of_max_fill_safety_wit_9 : max_fill_safety_wit_9.
Axiom proof_of_max_fill_safety_wit_10 : max_fill_safety_wit_10.
Axiom proof_of_max_fill_safety_wit_11 : max_fill_safety_wit_11.
Axiom proof_of_max_fill_safety_wit_12 : max_fill_safety_wit_12.
Axiom proof_of_max_fill_safety_wit_13 : max_fill_safety_wit_13.
Axiom proof_of_max_fill_safety_wit_14 : max_fill_safety_wit_14.
Axiom proof_of_max_fill_safety_wit_15 : max_fill_safety_wit_15.
Axiom proof_of_max_fill_entail_wit_1 : max_fill_entail_wit_1.
Axiom proof_of_max_fill_entail_wit_2 : max_fill_entail_wit_2.
Axiom proof_of_max_fill_entail_wit_3 : max_fill_entail_wit_3.
Axiom proof_of_max_fill_entail_wit_4 : max_fill_entail_wit_4.
Axiom proof_of_max_fill_entail_wit_5 : max_fill_entail_wit_5.
Axiom proof_of_max_fill_entail_wit_6_1 : max_fill_entail_wit_6_1.
Axiom proof_of_max_fill_entail_wit_6_2 : max_fill_entail_wit_6_2.
Axiom proof_of_max_fill_return_wit_1 : max_fill_return_wit_1.
Axiom proof_of_max_fill_partial_solve_wit_1 : max_fill_partial_solve_wit_1.

End VC_Correct.
