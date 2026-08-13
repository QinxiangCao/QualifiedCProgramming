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
From SimpleC.EE.QCP_demos_LLM Require Import array3_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array3_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.

(*----- Function touch_plane -----*)

Definition touch_plane_safety_wit_1 := 
forall (cols_count_pre: Z) (rows_count_pre: Z) (plane_pre: Z) (plane_rows: (@list (@list Z))) (PreH1 : (rows_count_pre = 3)) (PreH2 : (cols_count_pre = 4)) (PreH3 : ((Zlength (plane_rows)) = 3)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "plane" ) )) # Ptr  |-> plane_pre)
  **  ((( &( "rows_count" ) )) # Int  |-> rows_count_pre)
  **  ((( &( "cols_count" ) )) # Int  |-> cols_count_pre)
  **  (IntArray2.full plane_pre 3 4 plane_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition touch_plane_safety_wit_2 := 
forall (cols_count_pre: Z) (rows_count_pre: Z) (plane_pre: Z) (plane_rows: (@list (@list Z))) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 3)) (PreH3 : (rows_count_pre = 3)) (PreH4 : (cols_count_pre = 4)) (PreH5 : ((Zlength (plane_rows)) = 3)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "plane" ) )) # Ptr  |-> plane_pre)
  **  ((( &( "rows_count" ) )) # Int  |-> rows_count_pre)
  **  ((( &( "cols_count" ) )) # Int  |-> cols_count_pre)
  **  (IntArray2.full plane_pre 3 4 plane_rows )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition touch_plane_safety_wit_3 := 
forall (cols_count_pre: Z) (rows_count_pre: Z) (plane_pre: Z) (plane_rows: (@list (@list Z))) (i: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= i)) (PreH3 : (i <= 3)) (PreH4 : (rows_count_pre = 3)) (PreH5 : (cols_count_pre = 4)) (PreH6 : ((Zlength (plane_rows)) = 3)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "plane" ) )) # Ptr  |-> plane_pre)
  **  ((( &( "rows_count" ) )) # Int  |-> rows_count_pre)
  **  ((( &( "cols_count" ) )) # Int  |-> cols_count_pre)
  **  (IntArray2.full plane_pre 3 4 plane_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition touch_plane_safety_wit_4 := 
forall (cols_count_pre: Z) (rows_count_pre: Z) (plane_pre: Z) (plane_rows: (@list (@list Z))) (i: Z) (j: Z) (PreH1 : (0 <= j)) (PreH2 : (j <= 4)) (PreH3 : (rows_count_pre = 3)) (PreH4 : (cols_count_pre = 4)) (PreH5 : ((Zlength (plane_rows)) = 3)) (PreH6 : (0 <= i)) (PreH7 : (i < 3)) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "plane" ) )) # Ptr  |-> plane_pre)
  **  ((( &( "rows_count" ) )) # Int  |-> rows_count_pre)
  **  ((( &( "cols_count" ) )) # Int  |-> cols_count_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray2.full plane_pre 3 4 plane_rows )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition touch_plane_safety_wit_5 := 
forall (cols_count_pre: Z) (rows_count_pre: Z) (plane_pre: Z) (plane_rows: (@list (@list Z))) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < 4)) (PreH2 : (0 <= j)) (PreH3 : (j <= 4)) (PreH4 : (rows_count_pre = 3)) (PreH5 : (cols_count_pre = 4)) (PreH6 : ((Zlength (plane_rows)) = 3)) (PreH7 : (0 <= i)) (PreH8 : (i < 3)) ,
  (IntArray.full (plane_pre + (i * (sizeof(INT) * 4))) 4 (replace_Znth (j) ((Znth (j) ((Znth i plane_rows __default__List_Z)) (0))) ((Znth i plane_rows __default__List_Z))) )
  **  (IntArray2.missing_i plane_pre i 0 3 4 plane_rows )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "plane" ) )) # Ptr  |-> plane_pre)
  **  ((( &( "rows_count" ) )) # Int  |-> rows_count_pre)
  **  ((( &( "cols_count" ) )) # Int  |-> cols_count_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition touch_plane_safety_wit_6 := 
forall (cols_count_pre: Z) (rows_count_pre: Z) (plane_pre: Z) (plane_rows: (@list (@list Z))) (i: Z) (j: Z) (PreH1 : (j >= 4)) (PreH2 : (0 <= j)) (PreH3 : (j <= 4)) (PreH4 : (rows_count_pre = 3)) (PreH5 : (cols_count_pre = 4)) (PreH6 : ((Zlength (plane_rows)) = 3)) (PreH7 : (0 <= i)) (PreH8 : (i < 3)) ,
  ((( &( "plane" ) )) # Ptr  |-> plane_pre)
  **  ((( &( "rows_count" ) )) # Int  |-> rows_count_pre)
  **  ((( &( "cols_count" ) )) # Int  |-> cols_count_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray2.full plane_pre 3 4 plane_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition touch_plane_entail_wit_1 := 
forall (cols_count_pre: Z) (rows_count_pre: Z) (plane_pre: Z) (plane_rows: (@list (@list Z))) (PreH1 : (rows_count_pre = 3)) (PreH2 : (cols_count_pre = 4)) (PreH3 : ((Zlength (plane_rows)) = 3)) ,
  (IntArray2.full plane_pre 3 4 plane_rows )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 3) ” 
  &&  “ (rows_count_pre = 3) ” 
  &&  “ (cols_count_pre = 4) ” 
  &&  “ ((Zlength (plane_rows)) = 3) ”
  &&  (IntArray2.full plane_pre 3 4 plane_rows )
.

Definition touch_plane_entail_wit_2 := 
forall (cols_count_pre: Z) (rows_count_pre: Z) (plane_pre: Z) (plane_rows: (@list (@list Z))) (i: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= i)) (PreH3 : (i <= 3)) (PreH4 : (rows_count_pre = 3)) (PreH5 : (cols_count_pre = 4)) (PreH6 : ((Zlength (plane_rows)) = 3)) ,
  (IntArray2.full plane_pre 3 4 plane_rows )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 4) ” 
  &&  “ (rows_count_pre = 3) ” 
  &&  “ (cols_count_pre = 4) ” 
  &&  “ ((Zlength (plane_rows)) = 3) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 3) ”
  &&  (IntArray2.full plane_pre 3 4 plane_rows )
.

Definition touch_plane_entail_wit_3 := 
(
forall (cols_count_pre: Z) (rows_count_pre: Z) (plane_pre: Z) (plane_rows: (@list (@list Z))) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < 4)) (PreH2 : (0 <= j)) (PreH3 : (j <= 4)) (PreH4 : (rows_count_pre = 3)) (PreH5 : (cols_count_pre = 4)) (PreH6 : ((Zlength (plane_rows)) = 3)) (PreH7 : (0 <= i)) (PreH8 : (i < 3)) ,
  (IntArray.full (plane_pre + (i * (sizeof(INT) * 4))) 4 (replace_Znth (j) ((Znth (j) ((Znth i plane_rows __default__List_Z)) (0))) ((Znth i plane_rows __default__List_Z))) )
  **  (IntArray2.missing_i plane_pre i 0 3 4 plane_rows )
|--
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= 4) ” 
  &&  “ (rows_count_pre = 3) ” 
  &&  “ (cols_count_pre = 4) ” 
  &&  “ ((Zlength (plane_rows)) = 3) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 3) ”
  &&  (IntArray2.full plane_pre 3 4 plane_rows )
) \/
(
forall (cols_count_pre: Z) (rows_count_pre: Z) (plane_pre: Z) (plane_rows: (@list (@list Z))) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < 4)) (PreH2 : (0 <= j)) (PreH3 : (j <= 4)) (PreH4 : (rows_count_pre = 3)) (PreH5 : (cols_count_pre = 4)) (PreH6 : ((Zlength (plane_rows)) = 3)) (PreH7 : (0 <= i)) (PreH8 : (i < 3)) ,
  (IntArray.full (plane_pre + (i * (sizeof(INT) * 4))) 4 (replace_Znth (j) ((Znth (j) ((Znth i plane_rows __default__List_Z)) (0))) ((Znth i plane_rows __default__List_Z))) )
  **  (IntArray2.missing_i plane_pre i 0 3 4 plane_rows )
|--
  (IntArray2.full plane_pre 3 4 plane_rows )
).

Definition touch_plane_entail_wit_3_split_goal_spatial := 
forall (cols_count_pre: Z) (rows_count_pre: Z) (plane_pre: Z) (plane_rows: (@list (@list Z))) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < 4)) (PreH2 : (0 <= j)) (PreH3 : (j <= 4)) (PreH4 : (rows_count_pre = 3)) (PreH5 : (cols_count_pre = 4)) (PreH6 : ((Zlength (plane_rows)) = 3)) (PreH7 : (0 <= i)) (PreH8 : (i < 3)) ,
  (IntArray.full (plane_pre + (i * (sizeof(INT) * 4))) 4 (replace_Znth (j) ((Znth (j) ((Znth i plane_rows __default__List_Z)) (0))) ((Znth i plane_rows __default__List_Z))) )
  **  (IntArray2.missing_i plane_pre i 0 3 4 plane_rows )
|--
  (IntArray2.full plane_pre 3 4 plane_rows )
.

Definition touch_plane_entail_wit_4 := 
forall (cols_count_pre: Z) (rows_count_pre: Z) (plane_pre: Z) (plane_rows: (@list (@list Z))) (i: Z) (j: Z) (PreH1 : (j >= 4)) (PreH2 : (0 <= j)) (PreH3 : (j <= 4)) (PreH4 : (rows_count_pre = 3)) (PreH5 : (cols_count_pre = 4)) (PreH6 : ((Zlength (plane_rows)) = 3)) (PreH7 : (0 <= i)) (PreH8 : (i < 3)) ,
  (IntArray2.full plane_pre 3 4 plane_rows )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 3) ” 
  &&  “ (rows_count_pre = 3) ” 
  &&  “ (cols_count_pre = 4) ” 
  &&  “ ((Zlength (plane_rows)) = 3) ”
  &&  (IntArray2.full plane_pre 3 4 plane_rows )
.

Definition touch_plane_return_wit_1 := 
forall (cols_count_pre: Z) (rows_count_pre: Z) (plane_pre: Z) (plane_rows: (@list (@list Z))) (i: Z) (PreH1 : (i >= 3)) (PreH2 : (0 <= i)) (PreH3 : (i <= 3)) (PreH4 : (rows_count_pre = 3)) (PreH5 : (cols_count_pre = 4)) (PreH6 : ((Zlength (plane_rows)) = 3)) ,
  (IntArray2.full plane_pre 3 4 plane_rows )
|--
  (IntArray2.full plane_pre 3 4 plane_rows )
.

Definition touch_plane_partial_solve_wit_1 := 
forall (cols_count_pre: Z) (rows_count_pre: Z) (plane_pre: Z) (plane_rows: (@list (@list Z))) (i: Z) (j: Z)  __default__List_Z (PreH1 : (j < 4)) (PreH2 : (0 <= j)) (PreH3 : (j <= 4)) (PreH4 : (rows_count_pre = 3)) (PreH5 : (cols_count_pre = 4)) (PreH6 : ((Zlength (plane_rows)) = 3)) (PreH7 : (0 <= i)) (PreH8 : (i < 3)) ,
  (IntArray2.full plane_pre 3 4 plane_rows )
|--
  “ (j < 4) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= 4) ” 
  &&  “ (rows_count_pre = 3) ” 
  &&  “ (cols_count_pre = 4) ” 
  &&  “ ((Zlength (plane_rows)) = 3) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 3) ”
  &&  ((((plane_pre + (i * (sizeof(INT) * 4))) + (j * sizeof(INT)))) # Int  |-> (Znth (j) ((Znth i plane_rows __default__List_Z)) (0)))
  **  (IntArray.missing_i (plane_pre + (i * (sizeof(INT) * 4))) j 0 4 (Znth i plane_rows __default__List_Z) )
  **  (IntArray2.missing_i plane_pre i 0 3 4 plane_rows )
.

(*----- Function touch_graph_direct -----*)

Definition touch_graph_direct_safety_wit_1 := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (PreH1 : ((Zlength (cubes)) = 2)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition touch_graph_direct_safety_wit_2 := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 2)) (PreH3 : ((Zlength (cubes)) = 2)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition touch_graph_direct_safety_wit_3 := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (i: Z) (PreH1 : (i < 2)) (PreH2 : (0 <= i)) (PreH3 : (i <= 2)) (PreH4 : ((Zlength (cubes)) = 2)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition touch_graph_direct_safety_wit_4 := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (i: Z) (j: Z) (PreH1 : (0 <= j)) (PreH2 : (j <= 3)) (PreH3 : (0 <= i)) (PreH4 : (i < 2)) (PreH5 : ((Zlength (cubes)) = 2)) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition touch_graph_direct_safety_wit_5 := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (i: Z) (j: Z) (PreH1 : (j < 3)) (PreH2 : (0 <= j)) (PreH3 : (j <= 3)) (PreH4 : (0 <= i)) (PreH5 : (i < 2)) (PreH6 : ((Zlength (cubes)) = 2)) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition touch_graph_direct_safety_wit_6 := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (j: Z) (i: Z) (k: Z) (PreH1 : (0 <= k)) (PreH2 : (k <= 4)) (PreH3 : (0 <= i)) (PreH4 : (i < 2)) (PreH5 : (0 <= j)) (PreH6 : (j < 3)) (PreH7 : ((Zlength (cubes)) = 2)) ,
  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition touch_graph_direct_safety_wit_7 := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (j: Z) (i: Z) (k: Z)  __default__List_Z  __default__List__List_Z (PreH1 : (k < 4)) (PreH2 : (0 <= k)) (PreH3 : (k <= 4)) (PreH4 : (0 <= i)) (PreH5 : (i < 2)) (PreH6 : (0 <= j)) (PreH7 : (j < 3)) (PreH8 : ((Zlength (cubes)) = 2)) ,
  (IntArray.full ((&((box_pre)  # "GraphBox" ->ₛ "graph") + (i * ((sizeof(INT) * 4) * 3))) + (j * (sizeof(INT) * 4))) 4 (replace_Znth (k) ((Znth (k) ((Znth j (Znth i cubes __default__List__List_Z) __default__List_Z)) (0))) ((Znth j (Znth i cubes __default__List__List_Z) __default__List_Z))) )
  **  (IntArray2.missing_i (&((box_pre)  # "GraphBox" ->ₛ "graph") + (i * ((sizeof(INT) * 4) * 3))) j 0 3 4 (Znth i cubes __default__List__List_Z) )
  **  (IntArray3.missing_i &((box_pre)  # "GraphBox" ->ₛ "graph") i 0 2 3 4 cubes )
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition touch_graph_direct_safety_wit_8 := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (j: Z) (i: Z) (k: Z) (PreH1 : (k >= 4)) (PreH2 : (0 <= k)) (PreH3 : (k <= 4)) (PreH4 : (0 <= i)) (PreH5 : (i < 2)) (PreH6 : (0 <= j)) (PreH7 : (j < 3)) (PreH8 : ((Zlength (cubes)) = 2)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition touch_graph_direct_safety_wit_9 := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (i: Z) (j: Z) (PreH1 : (j >= 3)) (PreH2 : (0 <= j)) (PreH3 : (j <= 3)) (PreH4 : (0 <= i)) (PreH5 : (i < 2)) (PreH6 : ((Zlength (cubes)) = 2)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition touch_graph_direct_entail_wit_1 := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (PreH1 : ((Zlength (cubes)) = 2)) ,
  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 2) ” 
  &&  “ ((Zlength (cubes)) = 2) ”
  &&  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
.

Definition touch_graph_direct_entail_wit_2 := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (i: Z) (PreH1 : (i < 2)) (PreH2 : (0 <= i)) (PreH3 : (i <= 2)) (PreH4 : ((Zlength (cubes)) = 2)) ,
  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 3) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 2) ” 
  &&  “ ((Zlength (cubes)) = 2) ”
  &&  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
.

Definition touch_graph_direct_entail_wit_3 := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (i: Z) (j: Z) (PreH1 : (j < 3)) (PreH2 : (0 <= j)) (PreH3 : (j <= 3)) (PreH4 : (0 <= i)) (PreH5 : (i < 2)) (PreH6 : ((Zlength (cubes)) = 2)) ,
  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 4) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 2) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 3) ” 
  &&  “ ((Zlength (cubes)) = 2) ”
  &&  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
.

Definition touch_graph_direct_entail_wit_4 := 
(
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (j: Z) (i: Z) (k: Z)  __default__List_Z  __default__List__List_Z (PreH1 : (k < 4)) (PreH2 : (0 <= k)) (PreH3 : (k <= 4)) (PreH4 : (0 <= i)) (PreH5 : (i < 2)) (PreH6 : (0 <= j)) (PreH7 : (j < 3)) (PreH8 : ((Zlength (cubes)) = 2)) ,
  (IntArray.full ((&((box_pre)  # "GraphBox" ->ₛ "graph") + (i * ((sizeof(INT) * 4) * 3))) + (j * (sizeof(INT) * 4))) 4 (replace_Znth (k) ((Znth (k) ((Znth j (Znth i cubes __default__List__List_Z) __default__List_Z)) (0))) ((Znth j (Znth i cubes __default__List__List_Z) __default__List_Z))) )
  **  (IntArray2.missing_i (&((box_pre)  # "GraphBox" ->ₛ "graph") + (i * ((sizeof(INT) * 4) * 3))) j 0 3 4 (Znth i cubes __default__List__List_Z) )
  **  (IntArray3.missing_i &((box_pre)  # "GraphBox" ->ₛ "graph") i 0 2 3 4 cubes )
|--
  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= 4) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 2) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 3) ” 
  &&  “ ((Zlength (cubes)) = 2) ”
  &&  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
) \/
(
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (j: Z) (i: Z) (k: Z)  __default__List_Z  __default__List__List_Z (PreH1 : (k < 4)) (PreH2 : (0 <= k)) (PreH3 : (k <= 4)) (PreH4 : (0 <= i)) (PreH5 : (i < 2)) (PreH6 : (0 <= j)) (PreH7 : (j < 3)) (PreH8 : ((Zlength (cubes)) = 2)) ,
  (IntArray.full ((&((box_pre)  # "GraphBox" ->ₛ "graph") + (i * ((sizeof(INT) * 4) * 3))) + (j * (sizeof(INT) * 4))) 4 (replace_Znth (k) ((Znth (k) ((Znth j (Znth i cubes __default__List__List_Z) __default__List_Z)) (0))) ((Znth j (Znth i cubes __default__List__List_Z) __default__List_Z))) )
  **  (IntArray2.missing_i (&((box_pre)  # "GraphBox" ->ₛ "graph") + (i * ((sizeof(INT) * 4) * 3))) j 0 3 4 (Znth i cubes __default__List__List_Z) )
  **  (IntArray3.missing_i &((box_pre)  # "GraphBox" ->ₛ "graph") i 0 2 3 4 cubes )
|--
  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
).

Definition touch_graph_direct_entail_wit_4_split_goal_spatial := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (j: Z) (i: Z) (k: Z)  __default__List_Z  __default__List__List_Z (PreH1 : (k < 4)) (PreH2 : (0 <= k)) (PreH3 : (k <= 4)) (PreH4 : (0 <= i)) (PreH5 : (i < 2)) (PreH6 : (0 <= j)) (PreH7 : (j < 3)) (PreH8 : ((Zlength (cubes)) = 2)) ,
  (IntArray.full ((&((box_pre)  # "GraphBox" ->ₛ "graph") + (i * ((sizeof(INT) * 4) * 3))) + (j * (sizeof(INT) * 4))) 4 (replace_Znth (k) ((Znth (k) ((Znth j (Znth i cubes __default__List__List_Z) __default__List_Z)) (0))) ((Znth j (Znth i cubes __default__List__List_Z) __default__List_Z))) )
  **  (IntArray2.missing_i (&((box_pre)  # "GraphBox" ->ₛ "graph") + (i * ((sizeof(INT) * 4) * 3))) j 0 3 4 (Znth i cubes __default__List__List_Z) )
  **  (IntArray3.missing_i &((box_pre)  # "GraphBox" ->ₛ "graph") i 0 2 3 4 cubes )
|--
  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
.

Definition touch_graph_direct_entail_wit_5 := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (j: Z) (i: Z) (k: Z) (PreH1 : (k >= 4)) (PreH2 : (0 <= k)) (PreH3 : (k <= 4)) (PreH4 : (0 <= i)) (PreH5 : (i < 2)) (PreH6 : (0 <= j)) (PreH7 : (j < 3)) (PreH8 : ((Zlength (cubes)) = 2)) ,
  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= 3) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 2) ” 
  &&  “ ((Zlength (cubes)) = 2) ”
  &&  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
.

Definition touch_graph_direct_entail_wit_6 := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (i: Z) (j: Z) (PreH1 : (j >= 3)) (PreH2 : (0 <= j)) (PreH3 : (j <= 3)) (PreH4 : (0 <= i)) (PreH5 : (i < 2)) (PreH6 : ((Zlength (cubes)) = 2)) ,
  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 2) ” 
  &&  “ ((Zlength (cubes)) = 2) ”
  &&  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
.

Definition touch_graph_direct_return_wit_1 := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (i: Z) (PreH1 : (i >= 2)) (PreH2 : (0 <= i)) (PreH3 : (i <= 2)) (PreH4 : ((Zlength (cubes)) = 2)) ,
  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
.

Definition touch_graph_direct_partial_solve_wit_1 := 
forall (box_pre: Z) (cubes: (@list (@list (@list Z)))) (j: Z) (i: Z) (k: Z)  __default__List_Z  __default__List__List_Z (PreH1 : (k < 4)) (PreH2 : (0 <= k)) (PreH3 : (k <= 4)) (PreH4 : (0 <= i)) (PreH5 : (i < 2)) (PreH6 : (0 <= j)) (PreH7 : (j < 3)) (PreH8 : ((Zlength (cubes)) = 2)) ,
  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ (k < 4) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= 4) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 2) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 3) ” 
  &&  “ ((Zlength (cubes)) = 2) ”
  &&  (((((&((box_pre)  # "GraphBox" ->ₛ "graph") + (i * ((sizeof(INT) * 4) * 3))) + (j * (sizeof(INT) * 4))) + (k * sizeof(INT)))) # Int  |-> (Znth (k) ((Znth j (Znth i cubes __default__List__List_Z) __default__List_Z)) (0)))
  **  (IntArray.missing_i ((&((box_pre)  # "GraphBox" ->ₛ "graph") + (i * ((sizeof(INT) * 4) * 3))) + (j * (sizeof(INT) * 4))) k 0 4 (Znth j (Znth i cubes __default__List__List_Z) __default__List_Z) )
  **  (IntArray2.missing_i (&((box_pre)  # "GraphBox" ->ₛ "graph") + (i * ((sizeof(INT) * 4) * 3))) j 0 3 4 (Znth i cubes __default__List__List_Z) )
  **  (IntArray3.missing_i &((box_pre)  # "GraphBox" ->ₛ "graph") i 0 2 3 4 cubes )
.

(*----- Function touch_graph_plane -----*)

Definition touch_graph_plane_safety_wit_1 := 
forall (layer_pre: Z) (box_pre: Z) (cubes: (@list (@list (@list Z)))) (PreH1 : (0 <= layer_pre)) (PreH2 : (layer_pre < 2)) (PreH3 : ((Zlength (cubes)) = 2)) ,
  ((( &( "plane" ) )) # Ptr  |->_)
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  ((( &( "layer" ) )) # Int  |-> layer_pre)
  **  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition touch_graph_plane_safety_wit_2 := 
forall (layer_pre: Z) (box_pre: Z) (cubes: (@list (@list (@list Z)))) (PreH1 : (0 <= layer_pre)) (PreH2 : (layer_pre < 2)) (PreH3 : ((Zlength (cubes)) = 2)) ,
  ((( &( "plane" ) )) # Ptr  |-> ((&((box_pre)  # "GraphBox" ->ₛ "graph") + (layer_pre * ((sizeof(INT) * 4) * 3))) + (0 * (sizeof(INT) * 4))))
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  ((( &( "layer" ) )) # Int  |-> layer_pre)
  **  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition touch_graph_plane_safety_wit_3 := 
forall (layer_pre: Z) (box_pre: Z) (cubes: (@list (@list (@list Z)))) (PreH1 : (0 <= layer_pre)) (PreH2 : (layer_pre < 2)) (PreH3 : ((Zlength (cubes)) = 2)) ,
  ((( &( "plane" ) )) # Ptr  |-> ((&((box_pre)  # "GraphBox" ->ₛ "graph") + (layer_pre * ((sizeof(INT) * 4) * 3))) + (0 * (sizeof(INT) * 4))))
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  ((( &( "layer" ) )) # Int  |-> layer_pre)
  **  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition touch_graph_plane_return_wit_1 := 
forall (layer_pre: Z) (box_pre: Z) (cubes: (@list (@list (@list Z)))) (PreH1 : (0 <= layer_pre)) (PreH2 : (layer_pre < 2)) (PreH3 : ((Zlength (cubes)) = 2)) ,
  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
.

Definition touch_graph_plane_partial_solve_wit_1_pure := 
(
forall (layer_pre: Z) (box_pre: Z) (cubes: (@list (@list (@list Z))))  __default__List__List_Z (PreH1 : (0 <= layer_pre)) (PreH2 : (layer_pre < 2)) (PreH3 : ((Zlength (cubes)) = 2)) ,
  ((( &( "plane" ) )) # Ptr  |-> ((&((box_pre)  # "GraphBox" ->ₛ "graph") + (layer_pre * ((sizeof(INT) * 4) * 3))) + (0 * (sizeof(INT) * 4))))
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  ((( &( "layer" ) )) # Int  |-> layer_pre)
  **  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ (3 = 3) ” 
  &&  “ (4 = 4) ” 
  &&  “ ((Zlength ((Znth layer_pre cubes __default__List__List_Z))) = 3) ”
) \/
(
forall (layer_pre: Z) (box_pre: Z) (cubes: (@list (@list (@list Z))))  __default__List__List_Z (PreH1 : (layer_pre <= INT_MAX)) (PreH2 : (layer_pre >= INT_MIN)) (PreH3 : (0 <= layer_pre)) (PreH4 : (layer_pre < 2)) (PreH5 : ((Zlength (cubes)) = 2)) ,
  ((( &( "plane" ) )) # Ptr  |-> ((&((box_pre)  # "GraphBox" ->ₛ "graph") + (layer_pre * ((sizeof(INT) * 4) * 3))) + (0 * (sizeof(INT) * 4))))
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  ((( &( "layer" ) )) # Int  |-> layer_pre)
  **  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ ((Zlength ((Znth layer_pre cubes __default__List__List_Z))) = 3) ”
).

Definition touch_graph_plane_partial_solve_wit_1_pure_split_goal_1 := 
forall (layer_pre: Z) (box_pre: Z) (cubes: (@list (@list (@list Z))))  __default__List__List_Z (PreH1 : (layer_pre <= INT_MAX)) (PreH2 : (layer_pre >= INT_MIN)) (PreH3 : (0 <= layer_pre)) (PreH4 : (layer_pre < 2)) (PreH5 : ((Zlength (cubes)) = 2)) ,
  ((( &( "plane" ) )) # Ptr  |-> ((&((box_pre)  # "GraphBox" ->ₛ "graph") + (layer_pre * ((sizeof(INT) * 4) * 3))) + (0 * (sizeof(INT) * 4))))
  **  ((( &( "box" ) )) # Ptr  |-> box_pre)
  **  ((( &( "layer" ) )) # Int  |-> layer_pre)
  **  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ ((Zlength ((Znth layer_pre cubes __default__List__List_Z))) = 3) ”
.

Definition touch_graph_plane_partial_solve_wit_1_aux := 
forall (layer_pre: Z) (box_pre: Z) (cubes: (@list (@list (@list Z))))  __default__List__List_Z (PreH1 : (0 <= layer_pre)) (PreH2 : (layer_pre < 2)) (PreH3 : ((Zlength (cubes)) = 2)) ,
  (IntArray3.full &((box_pre)  # "GraphBox" ->ₛ "graph") 2 3 4 cubes )
|--
  “ (3 = 3) ” 
  &&  “ (4 = 4) ” 
  &&  “ ((Zlength ((Znth layer_pre cubes __default__List__List_Z))) = 3) ” 
  &&  “ (0 <= layer_pre) ” 
  &&  “ (layer_pre < 2) ” 
  &&  “ ((Zlength (cubes)) = 2) ”
  &&  (IntArray2.full ((&((box_pre)  # "GraphBox" ->ₛ "graph") + (layer_pre * ((sizeof(INT) * 4) * 3))) + (0 * (sizeof(INT) * 4))) 3 4 (Znth layer_pre cubes __default__List__List_Z) )
  **  (IntArray3.missing_i &((box_pre)  # "GraphBox" ->ₛ "graph") layer_pre 0 2 3 4 cubes )
.

Definition touch_graph_plane_partial_solve_wit_1 := touch_graph_plane_partial_solve_wit_1_pure -> touch_graph_plane_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include array3_Strategy_Correct.
Include array2_Strategy_Correct.
Include int_array_Strategy_Correct.

Axiom proof_of_touch_plane_safety_wit_1 : touch_plane_safety_wit_1.
Axiom proof_of_touch_plane_safety_wit_2 : touch_plane_safety_wit_2.
Axiom proof_of_touch_plane_safety_wit_3 : touch_plane_safety_wit_3.
Axiom proof_of_touch_plane_safety_wit_4 : touch_plane_safety_wit_4.
Axiom proof_of_touch_plane_safety_wit_5 : touch_plane_safety_wit_5.
Axiom proof_of_touch_plane_safety_wit_6 : touch_plane_safety_wit_6.
Axiom proof_of_touch_plane_entail_wit_1 : touch_plane_entail_wit_1.
Axiom proof_of_touch_plane_entail_wit_2 : touch_plane_entail_wit_2.
Axiom proof_of_touch_plane_entail_wit_3 : touch_plane_entail_wit_3.
Axiom proof_of_touch_plane_entail_wit_4 : touch_plane_entail_wit_4.
Axiom proof_of_touch_plane_return_wit_1 : touch_plane_return_wit_1.
Axiom proof_of_touch_plane_partial_solve_wit_1 : touch_plane_partial_solve_wit_1.
Axiom proof_of_touch_graph_direct_safety_wit_1 : touch_graph_direct_safety_wit_1.
Axiom proof_of_touch_graph_direct_safety_wit_2 : touch_graph_direct_safety_wit_2.
Axiom proof_of_touch_graph_direct_safety_wit_3 : touch_graph_direct_safety_wit_3.
Axiom proof_of_touch_graph_direct_safety_wit_4 : touch_graph_direct_safety_wit_4.
Axiom proof_of_touch_graph_direct_safety_wit_5 : touch_graph_direct_safety_wit_5.
Axiom proof_of_touch_graph_direct_safety_wit_6 : touch_graph_direct_safety_wit_6.
Axiom proof_of_touch_graph_direct_safety_wit_7 : touch_graph_direct_safety_wit_7.
Axiom proof_of_touch_graph_direct_safety_wit_8 : touch_graph_direct_safety_wit_8.
Axiom proof_of_touch_graph_direct_safety_wit_9 : touch_graph_direct_safety_wit_9.
Axiom proof_of_touch_graph_direct_entail_wit_1 : touch_graph_direct_entail_wit_1.
Axiom proof_of_touch_graph_direct_entail_wit_2 : touch_graph_direct_entail_wit_2.
Axiom proof_of_touch_graph_direct_entail_wit_3 : touch_graph_direct_entail_wit_3.
Axiom proof_of_touch_graph_direct_entail_wit_4 : touch_graph_direct_entail_wit_4.
Axiom proof_of_touch_graph_direct_entail_wit_5 : touch_graph_direct_entail_wit_5.
Axiom proof_of_touch_graph_direct_entail_wit_6 : touch_graph_direct_entail_wit_6.
Axiom proof_of_touch_graph_direct_return_wit_1 : touch_graph_direct_return_wit_1.
Axiom proof_of_touch_graph_direct_partial_solve_wit_1 : touch_graph_direct_partial_solve_wit_1.
Axiom proof_of_touch_graph_plane_safety_wit_1 : touch_graph_plane_safety_wit_1.
Axiom proof_of_touch_graph_plane_safety_wit_2 : touch_graph_plane_safety_wit_2.
Axiom proof_of_touch_graph_plane_safety_wit_3 : touch_graph_plane_safety_wit_3.
Axiom proof_of_touch_graph_plane_return_wit_1 : touch_graph_plane_return_wit_1.
Axiom proof_of_touch_graph_plane_partial_solve_wit_1_pure : touch_graph_plane_partial_solve_wit_1_pure.
Axiom proof_of_touch_graph_plane_partial_solve_wit_1 : touch_graph_plane_partial_solve_wit_1.

End VC_Correct.
