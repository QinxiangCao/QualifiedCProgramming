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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P085_498D_traffic_jams_in_the_land_lib.
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

(*----- Function pull -----*)

Definition pull_safety_wit_1 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (PeriodsOK arr )) (PreH9 : (CellsShaped cells )) (PreH10 : (RowIs cells (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH11 : (RowIs cells ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) ,
  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pull_safety_wit_2 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r <= 60)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cellsr )) (PreH12 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH13 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH14 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH15 : (RowsAgreeExcept v_pre cells cellsr )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (60 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 60) ”
.

Definition pull_safety_wit_3 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (r < 60)) (PreH2 : (1 <= v_pre)) (PreH3 : (((2 * v_pre ) + 1 ) < 400020)) (PreH4 : (1 <= lo)) (PreH5 : (lo <= mid)) (PreH6 : (mid < hi)) (PreH7 : (hi <= (Zlength (arr)))) (PreH8 : ((Zlength (arr)) <= 100000)) (PreH9 : (0 <= r)) (PreH10 : (r <= 60)) (PreH11 : (PeriodsOK arr )) (PreH12 : (CellsShaped cellsr )) (PreH13 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH14 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH15 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH16 : (RowsAgreeExcept v_pre cells cellsr )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ ((2 * v_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * v_pre )) ”
.

Definition pull_safety_wit_4 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (r < 60)) (PreH2 : (1 <= v_pre)) (PreH3 : (((2 * v_pre ) + 1 ) < 400020)) (PreH4 : (1 <= lo)) (PreH5 : (lo <= mid)) (PreH6 : (mid < hi)) (PreH7 : (hi <= (Zlength (arr)))) (PreH8 : ((Zlength (arr)) <= 100000)) (PreH9 : (0 <= r)) (PreH10 : (r <= 60)) (PreH11 : (PeriodsOK arr )) (PreH12 : (CellsShaped cellsr )) (PreH13 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH14 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH15 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH16 : (RowsAgreeExcept v_pre cells cellsr )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition pull_safety_wit_5 := 
(
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (left: Z)  __default__List__App_option_Z (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr )) (PreH17 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)))) (cellsr)) )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "left" ) )) # Int  |-> left)
|--
  “ ((left + (Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)) (((r + left ) % ( 60 ) ))) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + (Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)) (((r + left ) % ( 60 ) ))) )) ”
) \/
(
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (left: Z)  __default__List__App_option_Z (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr )) (PreH17 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)))) (cellsr)) )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "left" ) )) # Int  |-> left)
|--
  “ ((left + (Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)) (((r + left ) % ( 60 ) ))) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + (Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)) (((r + left ) % ( 60 ) ))) )) ”
).

Definition pull_safety_wit_5_split_goal_1 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (left: Z)  __default__List__App_option_Z (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr )) (PreH17 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)))) (cellsr)) )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "left" ) )) # Int  |-> left)
|--
  “ ((left + (Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)) (((r + left ) % ( 60 ) ))) ) <= INT_MAX) ”
.

Definition pull_safety_wit_5_split_goal_2 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (left: Z)  __default__List__App_option_Z (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr )) (PreH17 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)))) (cellsr)) )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "left" ) )) # Int  |-> left)
|--
  “ ((INT_MIN) <= (left + (Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)) (((r + left ) % ( 60 ) ))) )) ”
.

Definition pull_safety_wit_6 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (left: Z) (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr )) (PreH17 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (((r + left ) <> (INT_MIN)) \/ (60 <> (-1))) ” 
  &&  “ (60 <> 0) ”
.

Definition pull_safety_wit_7 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (left: Z) (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr )) (PreH17 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ ((r + left ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r + left )) ”
.

Definition pull_safety_wit_8 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (left: Z) (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr )) (PreH17 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (((2 * v_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * v_pre ) + 1 )) ”
.

Definition pull_safety_wit_9 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (left: Z) (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr )) (PreH17 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ ((2 * v_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * v_pre )) ”
.

Definition pull_safety_wit_10 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (left: Z) (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr )) (PreH17 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition pull_safety_wit_11 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (left: Z) (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr )) (PreH17 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pull_safety_wit_12 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (left: Z) (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr )) (PreH17 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (60 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 60) ”
.

Definition pull_safety_wit_13 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (left: Z)  __default__List__App_option_Z (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr )) (PreH17 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some ((left + (Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)) (((r + left ) % ( 60 ) ))) )))) ((Znth v_pre (Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)))) (cellsr)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)))) (cellsr)))) )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ ((r + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition pull_entail_wit_1 := 
(
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (PeriodsOK arr )) (PreH9 : (CellsShaped cells )) (PreH10 : (RowIs cells (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH11 : (RowIs cells ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  EX (cellsr: (@list (@list (@option Z)))) ,
  “ (1 <= v_pre) ” 
  &&  “ (((2 * v_pre ) + 1 ) < 400020) ” 
  &&  “ (1 <= lo) ” 
  &&  “ (lo <= mid) ” 
  &&  “ (mid < hi) ” 
  &&  “ (hi <= (Zlength (arr))) ” 
  &&  “ ((Zlength (arr)) <= 100000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cellsr ) ” 
  &&  “ (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) ) ” 
  &&  “ (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) ) ” 
  &&  “ (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) 0 ) ” 
  &&  “ (RowsAgreeExcept v_pre cells cellsr ) ”
  &&  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
) \/
(
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (PeriodsOK arr )) (PreH9 : (CellsShaped cells )) (PreH10 : (RowIs cells (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH11 : (RowIs cells ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) ,
  TT && emp 
|--
  “ (RowsAgreeExcept v_pre cells cells ) ” 
  &&  “ (RowPrefixIs cells v_pre (NodeSlice (arr) (lo) (hi)) 0 ) ”
  &&  emp
).

Definition pull_entail_wit_1_split_goal_1 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (PeriodsOK arr )) (PreH9 : (CellsShaped cells )) (PreH10 : (RowIs cells (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH11 : (RowIs cells ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) ,
  (RowsAgreeExcept v_pre cells cells )
.

Definition pull_entail_wit_1_split_goal_2 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (PeriodsOK arr )) (PreH9 : (CellsShaped cells )) (PreH10 : (RowIs cells (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH11 : (RowIs cells ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) ,
  (RowPrefixIs cells v_pre (NodeSlice (arr) (lo) (hi)) 0 )
.

Definition pull_entail_wit_2 := 
(
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : (r < 60)) (PreH2 : (1 <= v_pre)) (PreH3 : (((2 * v_pre ) + 1 ) < 400020)) (PreH4 : (1 <= lo)) (PreH5 : (lo <= mid)) (PreH6 : (mid < hi)) (PreH7 : (hi <= (Zlength (arr)))) (PreH8 : ((Zlength (arr)) <= 100000)) (PreH9 : (0 <= r)) (PreH10 : (r <= 60)) (PreH11 : (PeriodsOK arr )) (PreH12 : (CellsShaped cellsr )) (PreH13 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH14 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH15 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH16 : (RowsAgreeExcept v_pre cells cellsr )) ,
  ((((( &( "seg" ) ) + ((2 * v_pre ) * (sizeof(INT) * 60))) + (r * sizeof(INT)))) # Int  |-> (Array2.mixed_val ((Znth (2 * v_pre ) cellsr __default__List__App_option_Z)) (r)))
  **  (IntArray.mixed_missing_i (( &( "seg" ) ) + ((2 * v_pre ) * (sizeof(INT) * 60))) r 0 60 (Znth (2 * v_pre ) cellsr __default__List__App_option_Z) )
  **  (IntArray2.mixed_missing_i ( &( "seg" ) ) (2 * v_pre ) 0 400020 60 cellsr )
|--
  EX (cellsr_2: (@list (@list (@option Z)))) ,
  “ (1 <= v_pre) ” 
  &&  “ (((2 * v_pre ) + 1 ) < 400020) ” 
  &&  “ (1 <= lo) ” 
  &&  “ (lo <= mid) ” 
  &&  “ (mid < hi) ” 
  &&  “ (hi <= (Zlength (arr))) ” 
  &&  “ ((Zlength (arr)) <= 100000) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < 60) ” 
  &&  “ ((Array2.mixed_val ((Znth (2 * v_pre ) cellsr __default__List__App_option_Z)) (r)) = (delta ((NodeSlice (arr) (lo) (mid))) (r))) ” 
  &&  “ (1 <= (Array2.mixed_val ((Znth (2 * v_pre ) cellsr __default__List__App_option_Z)) (r))) ” 
  &&  “ ((Array2.mixed_val ((Znth (2 * v_pre ) cellsr __default__List__App_option_Z)) (r)) <= (2 * ((mid - lo ) + 1 ) )) ” 
  &&  “ (0 <= ((r + (Array2.mixed_val ((Znth (2 * v_pre ) cellsr __default__List__App_option_Z)) (r)) ) % ( 60 ) )) ” 
  &&  “ (((r + (Array2.mixed_val ((Znth (2 * v_pre ) cellsr __default__List__App_option_Z)) (r)) ) % ( 60 ) ) < 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cellsr_2 ) ” 
  &&  “ (RowIs cellsr_2 (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) ) ” 
  &&  “ (RowIs cellsr_2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) ) ” 
  &&  “ (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo) (hi)) r ) ” 
  &&  “ (RowsAgreeExcept v_pre cells cellsr_2 ) ”
  &&  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr_2 )
) \/
(
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth (2 * v_pre ) cellsr __default__List__App_option_Z)) (r)) <= INT_MAX)) (PreH2 : ((Array2.mixed_val ((Znth (2 * v_pre ) cellsr __default__List__App_option_Z)) (r)) >= INT_MIN)) (PreH3 : (r < 60)) (PreH4 : (1 <= v_pre)) (PreH5 : (((2 * v_pre ) + 1 ) < 400020)) (PreH6 : (1 <= lo)) (PreH7 : (lo <= mid)) (PreH8 : (mid < hi)) (PreH9 : (hi <= (Zlength (arr)))) (PreH10 : ((Zlength (arr)) <= 100000)) (PreH11 : (0 <= r)) (PreH12 : (r <= 60)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cellsr )) (PreH15 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH16 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH17 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH18 : (RowsAgreeExcept v_pre cells cellsr )) ,
  ((((( &( "seg" ) ) + ((2 * v_pre ) * (sizeof(INT) * 60))) + (r * sizeof(INT)))) # Int  |-> (Array2.mixed_val ((Znth (2 * v_pre ) cellsr __default__List__App_option_Z)) (r)))
  **  (IntArray.mixed_missing_i (( &( "seg" ) ) + ((2 * v_pre ) * (sizeof(INT) * 60))) r 0 60 (Znth (2 * v_pre ) cellsr __default__List__App_option_Z) )
  **  (IntArray2.mixed_missing_i ( &( "seg" ) ) (2 * v_pre ) 0 400020 60 cellsr )
|--
  EX (cellsr_2: (@list (@list (@option Z)))) ,
  “ (1 <= v_pre) ” 
  &&  “ (((2 * v_pre ) + 1 ) < 400020) ” 
  &&  “ (1 <= lo) ” 
  &&  “ (lo <= mid) ” 
  &&  “ (mid < hi) ” 
  &&  “ (hi <= (Zlength (arr))) ” 
  &&  “ ((Zlength (arr)) <= 100000) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < 60) ” 
  &&  “ ((Array2.mixed_val ((Znth (2 * v_pre ) cellsr __default__List__App_option_Z)) (r)) = (delta ((NodeSlice (arr) (lo) (mid))) (r))) ” 
  &&  “ (1 <= (Array2.mixed_val ((Znth (2 * v_pre ) cellsr __default__List__App_option_Z)) (r))) ” 
  &&  “ ((Array2.mixed_val ((Znth (2 * v_pre ) cellsr __default__List__App_option_Z)) (r)) <= (2 * ((mid - lo ) + 1 ) )) ” 
  &&  “ (0 <= ((r + (Array2.mixed_val ((Znth (2 * v_pre ) cellsr __default__List__App_option_Z)) (r)) ) % ( 60 ) )) ” 
  &&  “ (((r + (Array2.mixed_val ((Znth (2 * v_pre ) cellsr __default__List__App_option_Z)) (r)) ) % ( 60 ) ) < 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cellsr_2 ) ” 
  &&  “ (RowIs cellsr_2 (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) ) ” 
  &&  “ (RowIs cellsr_2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) ) ” 
  &&  “ (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo) (hi)) r ) ” 
  &&  “ (RowsAgreeExcept v_pre cells cellsr_2 ) ”
  &&  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr_2 )
).

Definition pull_entail_wit_3 := 
(
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z) (left: Z)  __default__List__App_option_Z (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr_2 )) (PreH17 : (RowIs cellsr_2 (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr_2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some ((left + (Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) ))) )))) ((Znth v_pre (Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)))) )
|--
  EX (cellsr: (@list (@list (@option Z)))) ,
  “ (1 <= v_pre) ” 
  &&  “ (((2 * v_pre ) + 1 ) < 400020) ” 
  &&  “ (1 <= lo) ” 
  &&  “ (lo <= mid) ” 
  &&  “ (mid < hi) ” 
  &&  “ (hi <= (Zlength (arr))) ” 
  &&  “ ((Zlength (arr)) <= 100000) ” 
  &&  “ (0 <= (r + 1 )) ” 
  &&  “ ((r + 1 ) <= 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cellsr ) ” 
  &&  “ (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) ) ” 
  &&  “ (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) ) ” 
  &&  “ (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) (r + 1 ) ) ” 
  &&  “ (RowsAgreeExcept v_pre cells cellsr ) ”
  &&  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
) \/
(
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z) (left: Z)  __default__List__App_option_Z (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr_2 )) (PreH17 : (RowIs cellsr_2 (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr_2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  TT && emp 
|--
  “ (RowsAgreeExcept v_pre cells (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some ((left + (Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) ))) )))) ((Znth v_pre (Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)))) ) ” 
  &&  “ (RowPrefixIs (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some ((left + (Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) ))) )))) ((Znth v_pre (Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)))) v_pre (NodeSlice (arr) (lo) (hi)) (r + 1 ) ) ” 
  &&  “ (RowIs (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some ((left + (Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) ))) )))) ((Znth v_pre (Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)))) ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) ) ” 
  &&  “ (RowIs (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some ((left + (Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) ))) )))) ((Znth v_pre (Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)))) (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) ) ” 
  &&  “ (CellsShaped (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some ((left + (Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) ))) )))) ((Znth v_pre (Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)))) ) ”
  &&  emp
).

Definition pull_entail_wit_3_split_goal_1 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z) (left: Z)  __default__List__App_option_Z (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr_2 )) (PreH17 : (RowIs cellsr_2 (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr_2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (RowsAgreeExcept v_pre cells (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some ((left + (Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) ))) )))) ((Znth v_pre (Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)))) )
.

Definition pull_entail_wit_3_split_goal_2 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z) (left: Z)  __default__List__App_option_Z (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr_2 )) (PreH17 : (RowIs cellsr_2 (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr_2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (RowPrefixIs (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some ((left + (Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) ))) )))) ((Znth v_pre (Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)))) v_pre (NodeSlice (arr) (lo) (hi)) (r + 1 ) )
.

Definition pull_entail_wit_3_split_goal_3 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z) (left: Z)  __default__List__App_option_Z (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr_2 )) (PreH17 : (RowIs cellsr_2 (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr_2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (RowIs (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some ((left + (Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) ))) )))) ((Znth v_pre (Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)))) ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )
.

Definition pull_entail_wit_3_split_goal_4 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z) (left: Z)  __default__List__App_option_Z (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr_2 )) (PreH17 : (RowIs cellsr_2 (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr_2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (RowIs (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some ((left + (Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) ))) )))) ((Znth v_pre (Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)))) (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )
.

Definition pull_entail_wit_3_split_goal_5 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z) (left: Z)  __default__List__App_option_Z (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr_2 )) (PreH17 : (RowIs cellsr_2 (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr_2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (CellsShaped (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some ((left + (Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) ))) )))) ((Znth v_pre (Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr_2 __default__List__App_option_Z)))) (cellsr_2)))) )
.

Definition pull_return_wit_1 := 
(
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (r >= 60)) (PreH2 : (1 <= v_pre)) (PreH3 : (((2 * v_pre ) + 1 ) < 400020)) (PreH4 : (1 <= lo)) (PreH5 : (lo <= mid)) (PreH6 : (mid < hi)) (PreH7 : (hi <= (Zlength (arr)))) (PreH8 : ((Zlength (arr)) <= 100000)) (PreH9 : (0 <= r)) (PreH10 : (r <= 60)) (PreH11 : (PeriodsOK arr )) (PreH12 : (CellsShaped cellsr )) (PreH13 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH14 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH15 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH16 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  EX (cells1: (@list (@list (@option Z)))) ,
  “ (CellsShaped cells1 ) ” 
  &&  “ (RowIs cells1 v_pre (NodeSlice (arr) (lo) (hi)) ) ” 
  &&  “ (RowsAgreeExcept v_pre cells cells1 ) ”
  &&  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
) \/
(
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (r >= 60)) (PreH2 : (1 <= v_pre)) (PreH3 : (((2 * v_pre ) + 1 ) < 400020)) (PreH4 : (1 <= lo)) (PreH5 : (lo <= mid)) (PreH6 : (mid < hi)) (PreH7 : (hi <= (Zlength (arr)))) (PreH8 : ((Zlength (arr)) <= 100000)) (PreH9 : (0 <= r)) (PreH10 : (r <= 60)) (PreH11 : (PeriodsOK arr )) (PreH12 : (CellsShaped cellsr )) (PreH13 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH14 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH15 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH16 : (RowsAgreeExcept v_pre cells cellsr )) ,
  TT && emp 
|--
  “ (RowIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) ) ”
  &&  emp
).

Definition pull_return_wit_1_split_goal_1 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (r >= 60)) (PreH2 : (1 <= v_pre)) (PreH3 : (((2 * v_pre ) + 1 ) < 400020)) (PreH4 : (1 <= lo)) (PreH5 : (lo <= mid)) (PreH6 : (mid < hi)) (PreH7 : (hi <= (Zlength (arr)))) (PreH8 : ((Zlength (arr)) <= 100000)) (PreH9 : (0 <= r)) (PreH10 : (r <= 60)) (PreH11 : (PeriodsOK arr )) (PreH12 : (CellsShaped cellsr )) (PreH13 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH14 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH15 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH16 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (RowIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) )
.

Definition pull_partial_solve_wit_1_pure := 
(
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : (r < 60)) (PreH2 : (1 <= v_pre)) (PreH3 : (((2 * v_pre ) + 1 ) < 400020)) (PreH4 : (1 <= lo)) (PreH5 : (lo <= mid)) (PreH6 : (mid < hi)) (PreH7 : (hi <= (Zlength (arr)))) (PreH8 : ((Zlength (arr)) <= 100000)) (PreH9 : (0 <= r)) (PreH10 : (r <= 60)) (PreH11 : (PeriodsOK arr )) (PreH12 : (CellsShaped cellsr )) (PreH13 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH14 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH15 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH16 : (RowsAgreeExcept v_pre cells cellsr )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (Array2.mixed_def (Znth (2 * v_pre ) cellsr __default__List__App_option_Z) r ) ”
) \/
(
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : (r <= INT_MAX)) (PreH2 : (v_pre <= INT_MAX)) (PreH3 : (r >= INT_MIN)) (PreH4 : (v_pre >= INT_MIN)) (PreH5 : (r < 60)) (PreH6 : (1 <= v_pre)) (PreH7 : (((2 * v_pre ) + 1 ) < 400020)) (PreH8 : (1 <= lo)) (PreH9 : (lo <= mid)) (PreH10 : (mid < hi)) (PreH11 : (hi <= (Zlength (arr)))) (PreH12 : ((Zlength (arr)) <= 100000)) (PreH13 : (0 <= r)) (PreH14 : (r <= 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr )) (PreH17 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (Array2.mixed_def (Znth (2 * v_pre ) cellsr __default__List__App_option_Z) r ) ”
).

Definition pull_partial_solve_wit_1_pure_split_goal_1 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : (r <= INT_MAX)) (PreH2 : (v_pre <= INT_MAX)) (PreH3 : (r >= INT_MIN)) (PreH4 : (v_pre >= INT_MIN)) (PreH5 : (r < 60)) (PreH6 : (1 <= v_pre)) (PreH7 : (((2 * v_pre ) + 1 ) < 400020)) (PreH8 : (1 <= lo)) (PreH9 : (lo <= mid)) (PreH10 : (mid < hi)) (PreH11 : (hi <= (Zlength (arr)))) (PreH12 : ((Zlength (arr)) <= 100000)) (PreH13 : (0 <= r)) (PreH14 : (r <= 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr )) (PreH17 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (Array2.mixed_def (Znth (2 * v_pre ) cellsr __default__List__App_option_Z) r ) ”
.

Definition pull_partial_solve_wit_1_aux := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : (r < 60)) (PreH2 : (1 <= v_pre)) (PreH3 : (((2 * v_pre ) + 1 ) < 400020)) (PreH4 : (1 <= lo)) (PreH5 : (lo <= mid)) (PreH6 : (mid < hi)) (PreH7 : (hi <= (Zlength (arr)))) (PreH8 : ((Zlength (arr)) <= 100000)) (PreH9 : (0 <= r)) (PreH10 : (r <= 60)) (PreH11 : (PeriodsOK arr )) (PreH12 : (CellsShaped cellsr )) (PreH13 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH14 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH15 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH16 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (Array2.mixed_def (Znth (2 * v_pre ) cellsr __default__List__App_option_Z) r ) ” 
  &&  “ (r < 60) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (((2 * v_pre ) + 1 ) < 400020) ” 
  &&  “ (1 <= lo) ” 
  &&  “ (lo <= mid) ” 
  &&  “ (mid < hi) ” 
  &&  “ (hi <= (Zlength (arr))) ” 
  &&  “ ((Zlength (arr)) <= 100000) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r <= 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cellsr ) ” 
  &&  “ (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) ) ” 
  &&  “ (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) ) ” 
  &&  “ (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r ) ” 
  &&  “ (RowsAgreeExcept v_pre cells cellsr ) ”
  &&  ((((( &( "seg" ) ) + ((2 * v_pre ) * (sizeof(INT) * 60))) + (r * sizeof(INT)))) # Int  |-> (Array2.mixed_val ((Znth (2 * v_pre ) cellsr __default__List__App_option_Z)) (r)))
  **  (IntArray.mixed_missing_i (( &( "seg" ) ) + ((2 * v_pre ) * (sizeof(INT) * 60))) r 0 60 (Znth (2 * v_pre ) cellsr __default__List__App_option_Z) )
  **  (IntArray2.mixed_missing_i ( &( "seg" ) ) (2 * v_pre ) 0 400020 60 cellsr )
.

Definition pull_partial_solve_wit_1 := pull_partial_solve_wit_1_pure -> pull_partial_solve_wit_1_aux.

Definition pull_partial_solve_wit_2_pure := 
(
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (left: Z)  __default__List__App_option_Z (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr )) (PreH17 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (Array2.mixed_def (Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z) ((r + left ) % ( 60 ) ) ) ”
) \/
(
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (left: Z)  __default__List__App_option_Z (PreH1 : (left <= INT_MAX)) (PreH2 : (r <= INT_MAX)) (PreH3 : (v_pre <= INT_MAX)) (PreH4 : (left >= INT_MIN)) (PreH5 : (r >= INT_MIN)) (PreH6 : (v_pre >= INT_MIN)) (PreH7 : (1 <= v_pre)) (PreH8 : (((2 * v_pre ) + 1 ) < 400020)) (PreH9 : (1 <= lo)) (PreH10 : (lo <= mid)) (PreH11 : (mid < hi)) (PreH12 : (hi <= (Zlength (arr)))) (PreH13 : ((Zlength (arr)) <= 100000)) (PreH14 : (0 <= r)) (PreH15 : (r < 60)) (PreH16 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH17 : (1 <= left)) (PreH18 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH19 : (0 <= ((r + left ) % ( 60 ) ))) (PreH20 : (((r + left ) % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cellsr )) (PreH23 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH24 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH25 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH26 : (RowsAgreeExcept v_pre cells cellsr )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (Array2.mixed_def (Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z) ((r + left ) % ( 60 ) ) ) ”
).

Definition pull_partial_solve_wit_2_pure_split_goal_1 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (left: Z)  __default__List__App_option_Z (PreH1 : (left <= INT_MAX)) (PreH2 : (r <= INT_MAX)) (PreH3 : (v_pre <= INT_MAX)) (PreH4 : (left >= INT_MIN)) (PreH5 : (r >= INT_MIN)) (PreH6 : (v_pre >= INT_MIN)) (PreH7 : (1 <= v_pre)) (PreH8 : (((2 * v_pre ) + 1 ) < 400020)) (PreH9 : (1 <= lo)) (PreH10 : (lo <= mid)) (PreH11 : (mid < hi)) (PreH12 : (hi <= (Zlength (arr)))) (PreH13 : ((Zlength (arr)) <= 100000)) (PreH14 : (0 <= r)) (PreH15 : (r < 60)) (PreH16 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH17 : (1 <= left)) (PreH18 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH19 : (0 <= ((r + left ) % ( 60 ) ))) (PreH20 : (((r + left ) % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cellsr )) (PreH23 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH24 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH25 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH26 : (RowsAgreeExcept v_pre cells cellsr )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (Array2.mixed_def (Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z) ((r + left ) % ( 60 ) ) ) ”
.

Definition pull_partial_solve_wit_2_aux := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (left: Z)  __default__List__App_option_Z (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr )) (PreH17 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (Array2.mixed_def (Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z) ((r + left ) % ( 60 ) ) ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (((2 * v_pre ) + 1 ) < 400020) ” 
  &&  “ (1 <= lo) ” 
  &&  “ (lo <= mid) ” 
  &&  “ (mid < hi) ” 
  &&  “ (hi <= (Zlength (arr))) ” 
  &&  “ ((Zlength (arr)) <= 100000) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < 60) ” 
  &&  “ (left = (delta ((NodeSlice (arr) (lo) (mid))) (r))) ” 
  &&  “ (1 <= left) ” 
  &&  “ (left <= (2 * ((mid - lo ) + 1 ) )) ” 
  &&  “ (0 <= ((r + left ) % ( 60 ) )) ” 
  &&  “ (((r + left ) % ( 60 ) ) < 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cellsr ) ” 
  &&  “ (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) ) ” 
  &&  “ (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) ) ” 
  &&  “ (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r ) ” 
  &&  “ (RowsAgreeExcept v_pre cells cellsr ) ”
  &&  ((((( &( "seg" ) ) + (((2 * v_pre ) + 1 ) * (sizeof(INT) * 60))) + (((r + left ) % ( 60 ) ) * sizeof(INT)))) # Int  |-> (Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)) (((r + left ) % ( 60 ) ))))
  **  (IntArray.mixed_missing_i (( &( "seg" ) ) + (((2 * v_pre ) + 1 ) * (sizeof(INT) * 60))) ((r + left ) % ( 60 ) ) 0 60 (Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z) )
  **  (IntArray2.mixed_missing_i ( &( "seg" ) ) ((2 * v_pre ) + 1 ) 0 400020 60 cellsr )
.

Definition pull_partial_solve_wit_2 := pull_partial_solve_wit_2_pure -> pull_partial_solve_wit_2_aux.

Definition pull_partial_solve_wit_3 := 
forall (v_pre: Z) (hi: Z) (mid: Z) (lo: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (left: Z)  __default__List__App_option_Z (PreH1 : (1 <= v_pre)) (PreH2 : (((2 * v_pre ) + 1 ) < 400020)) (PreH3 : (1 <= lo)) (PreH4 : (lo <= mid)) (PreH5 : (mid < hi)) (PreH6 : (hi <= (Zlength (arr)))) (PreH7 : ((Zlength (arr)) <= 100000)) (PreH8 : (0 <= r)) (PreH9 : (r < 60)) (PreH10 : (left = (delta ((NodeSlice (arr) (lo) (mid))) (r)))) (PreH11 : (1 <= left)) (PreH12 : (left <= (2 * ((mid - lo ) + 1 ) ))) (PreH13 : (0 <= ((r + left ) % ( 60 ) ))) (PreH14 : (((r + left ) % ( 60 ) ) < 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr )) (PreH17 : (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) )) (PreH18 : (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)))) (cellsr)) )
|--
  “ (1 <= v_pre) ” 
  &&  “ (((2 * v_pre ) + 1 ) < 400020) ” 
  &&  “ (1 <= lo) ” 
  &&  “ (lo <= mid) ” 
  &&  “ (mid < hi) ” 
  &&  “ (hi <= (Zlength (arr))) ” 
  &&  “ ((Zlength (arr)) <= 100000) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < 60) ” 
  &&  “ (left = (delta ((NodeSlice (arr) (lo) (mid))) (r))) ” 
  &&  “ (1 <= left) ” 
  &&  “ (left <= (2 * ((mid - lo ) + 1 ) )) ” 
  &&  “ (0 <= ((r + left ) % ( 60 ) )) ” 
  &&  “ (((r + left ) % ( 60 ) ) < 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cellsr ) ” 
  &&  “ (RowIs cellsr (2 * v_pre ) (NodeSlice (arr) (lo) (mid)) ) ” 
  &&  “ (RowIs cellsr ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi)) ) ” 
  &&  “ (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo) (hi)) r ) ” 
  &&  “ (RowsAgreeExcept v_pre cells cellsr ) ”
  &&  ((((( &( "seg" ) ) + (v_pre * (sizeof(INT) * 60))) + (r * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i (( &( "seg" ) ) + (v_pre * (sizeof(INT) * 60))) r 0 60 (Znth v_pre (Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)))) (cellsr)) __default__List__App_option_Z) )
  **  (IntArray2.mixed_missing_i ( &( "seg" ) ) v_pre 0 400020 60 (Array2.replace_mixed_row (((2 * v_pre ) + 1 )) ((replace_Znth (((r + left ) % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)) (((r + left ) % ( 60 ) )))))) ((Znth ((2 * v_pre ) + 1 ) cellsr __default__List__App_option_Z)))) (cellsr)) )
.

(*----- Function build -----*)

Definition build_safety_wit_1 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_safety_wit_2 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (1 <= v_pre)) (PreH4 : (v_pre < 400020)) (PreH5 : (1 <= lo_pre)) (PreH6 : (lo_pre <= n)) (PreH7 : (hi_pre <= n)) (PreH8 : (n = (Zlength (arr)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 100000)) (PreH11 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH12 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH13 : (0 <= r)) (PreH14 : (r <= 60)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cellsr )) (PreH17 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH18 : (RowsAgreeExcept v_pre cells cellsr )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (60 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 60) ”
.

Definition build_safety_wit_3 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) = 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (2))) ((Znth v_pre cellsr __default__List__App_option_Z)))) (cellsr)) )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ ((r + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition build_safety_wit_4 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) <> 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (1))) ((Znth v_pre cellsr __default__List__App_option_Z)))) (cellsr)) )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ ((r + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition build_safety_wit_5 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (r < 60)) (PreH2 : (lo_pre = hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= n)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH13 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH14 : (0 <= r)) (PreH15 : (r <= 60)) (PreH16 : (PeriodsOK arr )) (PreH17 : (CellsShaped cellsr )) (PreH18 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH19 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ ((r <> (INT_MIN)) \/ ((Znth (lo_pre - 1 ) arr 0) <> (-1))) ” 
  &&  “ ((Znth (lo_pre - 1 ) arr 0) <> 0) ”
.

Definition build_safety_wit_6 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (r < 60)) (PreH2 : (lo_pre = hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= n)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH13 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH14 : (0 <= r)) (PreH15 : (r <= 60)) (PreH16 : (PeriodsOK arr )) (PreH17 : (CellsShaped cellsr )) (PreH18 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH19 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_safety_wit_7 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) = 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition build_safety_wit_8 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) <> 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_safety_wit_9 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (((lo_pre + hi_pre ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition build_safety_wit_10 := 
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((lo_pre + hi_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lo_pre + hi_pre )) ”
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((lo_pre + hi_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lo_pre + hi_pre )) ”
).

Definition build_safety_wit_10_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((lo_pre + hi_pre ) <= INT_MAX) ”
.

Definition build_safety_wit_10_split_goal_2 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((INT_MIN) <= (lo_pre + hi_pre )) ”
.

Definition build_safety_wit_11 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition build_safety_wit_12 := 
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((2 * v_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * v_pre )) ”
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((2 * v_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * v_pre )) ”
).

Definition build_safety_wit_12_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((2 * v_pre ) <= INT_MAX) ”
.

Definition build_safety_wit_12_split_goal_2 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((INT_MIN) <= (2 * v_pre )) ”
.

Definition build_safety_wit_13 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition build_safety_wit_14 := 
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (lo_pre <> hi_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (hi_pre <= n)) (PreH7 : (n = (Zlength (arr)))) (PreH8 : (1 <= n)) (PreH9 : (n <= 100000)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ ((((lo_pre + hi_pre ) ÷ 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((lo_pre + hi_pre ) ÷ 2 ) + 1 )) ”
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (lo_pre <> hi_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (hi_pre <= n)) (PreH7 : (n = (Zlength (arr)))) (PreH8 : (1 <= n)) (PreH9 : (n <= 100000)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ ((((lo_pre + hi_pre ) ÷ 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((lo_pre + hi_pre ) ÷ 2 ) + 1 )) ”
).

Definition build_safety_wit_14_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (lo_pre <> hi_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (hi_pre <= n)) (PreH7 : (n = (Zlength (arr)))) (PreH8 : (1 <= n)) (PreH9 : (n <= 100000)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ ((((lo_pre + hi_pre ) ÷ 2 ) + 1 ) <= INT_MAX) ”
.

Definition build_safety_wit_14_split_goal_2 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (lo_pre <> hi_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (hi_pre <= n)) (PreH7 : (n = (Zlength (arr)))) (PreH8 : (1 <= n)) (PreH9 : (n <= 100000)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ ((INT_MIN) <= (((lo_pre + hi_pre ) ÷ 2 ) + 1 )) ”
.

Definition build_safety_wit_15 := 
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (lo_pre <> hi_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (hi_pre <= n)) (PreH7 : (n = (Zlength (arr)))) (PreH8 : (1 <= n)) (PreH9 : (n <= 100000)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ (((2 * v_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * v_pre ) + 1 )) ”
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (lo_pre <> hi_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (hi_pre <= n)) (PreH7 : (n = (Zlength (arr)))) (PreH8 : (1 <= n)) (PreH9 : (n <= 100000)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ (((2 * v_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * v_pre ) + 1 )) ”
).

Definition build_safety_wit_15_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (lo_pre <> hi_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (hi_pre <= n)) (PreH7 : (n = (Zlength (arr)))) (PreH8 : (1 <= n)) (PreH9 : (n <= 100000)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ (((2 * v_pre ) + 1 ) <= INT_MAX) ”
.

Definition build_safety_wit_15_split_goal_2 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (lo_pre <> hi_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (hi_pre <= n)) (PreH7 : (n = (Zlength (arr)))) (PreH8 : (1 <= n)) (PreH9 : (n <= 100000)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ ((INT_MIN) <= ((2 * v_pre ) + 1 )) ”
.

Definition build_safety_wit_16 := 
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (lo_pre <> hi_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (hi_pre <= n)) (PreH7 : (n = (Zlength (arr)))) (PreH8 : (1 <= n)) (PreH9 : (n <= 100000)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ ((2 * v_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * v_pre )) ”
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (lo_pre <> hi_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (hi_pre <= n)) (PreH7 : (n = (Zlength (arr)))) (PreH8 : (1 <= n)) (PreH9 : (n <= 100000)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ ((2 * v_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * v_pre )) ”
).

Definition build_safety_wit_16_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (lo_pre <> hi_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (hi_pre <= n)) (PreH7 : (n = (Zlength (arr)))) (PreH8 : (1 <= n)) (PreH9 : (n <= 100000)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ ((2 * v_pre ) <= INT_MAX) ”
.

Definition build_safety_wit_16_split_goal_2 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (lo_pre <> hi_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (hi_pre <= n)) (PreH7 : (n = (Zlength (arr)))) (PreH8 : (1 <= n)) (PreH9 : (n <= 100000)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ ((INT_MIN) <= (2 * v_pre )) ”
.

Definition build_safety_wit_17 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (lo_pre <> hi_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (hi_pre <= n)) (PreH7 : (n = (Zlength (arr)))) (PreH8 : (1 <= n)) (PreH9 : (n <= 100000)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition build_safety_wit_18 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (lo_pre <> hi_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (hi_pre <= n)) (PreH7 : (n = (Zlength (arr)))) (PreH8 : (1 <= n)) (PreH9 : (n <= 100000)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_safety_wit_19 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (lo_pre <> hi_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (hi_pre <= n)) (PreH7 : (n = (Zlength (arr)))) (PreH8 : (1 <= n)) (PreH9 : (n <= 100000)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_entail_wit_1 := 
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  EX (cellsr: (@list (@list (@option Z)))) ,
  “ (lo_pre = hi_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= n) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (2 <= (Znth ((lo_pre - 1 )) (arr) (0))) ” 
  &&  “ ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cellsr ) ” 
  &&  “ (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) 0 ) ” 
  &&  “ (RowsAgreeExcept v_pre cells cellsr ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  TT && emp 
|--
  “ (RowsAgreeExcept v_pre cells cells ) ” 
  &&  “ (RowPrefixIs cells v_pre (NodeSlice (arr) (hi_pre) (hi_pre)) 0 ) ” 
  &&  “ ((Znth ((hi_pre - 1 )) (arr) (0)) <= 6) ” 
  &&  “ (2 <= (Znth ((hi_pre - 1 )) (arr) (0))) ” 
  &&  “ (1 <= hi_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= v_pre) ”
  &&  emp
).

Definition build_entail_wit_1_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  (RowsAgreeExcept v_pre cells cells )
.

Definition build_entail_wit_1_split_goal_2 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  (RowPrefixIs cells v_pre (NodeSlice (arr) (hi_pre) (hi_pre)) 0 )
.

Definition build_entail_wit_1_split_goal_3 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  ((Znth ((hi_pre - 1 )) (arr) (0)) <= 6)
.

Definition build_entail_wit_1_split_goal_4 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  (2 <= (Znth ((hi_pre - 1 )) (arr) (0)))
.

Definition build_entail_wit_1_split_goal_5 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  (1 <= hi_pre)
.

Definition build_entail_wit_1_split_goal_6 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  (v_pre < 400020)
.

Definition build_entail_wit_1_split_goal_7 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  (1 <= v_pre)
.

Definition build_entail_wit_2_1 := 
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) = 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr_2 )) (PreH19 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (2))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
|--
  EX (cellsr: (@list (@list (@option Z)))) ,
  “ (lo_pre = hi_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= n) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (2 <= (Znth ((lo_pre - 1 )) (arr) (0))) ” 
  &&  “ ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6) ” 
  &&  “ (0 <= (r + 1 )) ” 
  &&  “ ((r + 1 ) <= 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cellsr ) ” 
  &&  “ (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) (r + 1 ) ) ” 
  &&  “ (RowsAgreeExcept v_pre cells cellsr ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) = 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr_2 )) (PreH19 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  TT && emp 
|--
  “ (RowsAgreeExcept v_pre cells (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (2))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) ) ” 
  &&  “ (RowPrefixIs (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (2))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) v_pre (NodeSlice (arr) (hi_pre) (hi_pre)) (r + 1 ) ) ” 
  &&  “ (CellsShaped (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (2))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) ) ”
  &&  emp
).

Definition build_entail_wit_2_1_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) = 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr_2 )) (PreH19 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (RowsAgreeExcept v_pre cells (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (2))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) )
.

Definition build_entail_wit_2_1_split_goal_2 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) = 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr_2 )) (PreH19 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (RowPrefixIs (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (2))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) v_pre (NodeSlice (arr) (hi_pre) (hi_pre)) (r + 1 ) )
.

Definition build_entail_wit_2_1_split_goal_3 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) = 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr_2 )) (PreH19 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (CellsShaped (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (2))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) )
.

Definition build_entail_wit_2_2 := 
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) <> 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr_2 )) (PreH19 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (1))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
|--
  EX (cellsr: (@list (@list (@option Z)))) ,
  “ (lo_pre = hi_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= n) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (2 <= (Znth ((lo_pre - 1 )) (arr) (0))) ” 
  &&  “ ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6) ” 
  &&  “ (0 <= (r + 1 )) ” 
  &&  “ ((r + 1 ) <= 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cellsr ) ” 
  &&  “ (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) (r + 1 ) ) ” 
  &&  “ (RowsAgreeExcept v_pre cells cellsr ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) <> 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr_2 )) (PreH19 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  TT && emp 
|--
  “ (RowsAgreeExcept v_pre cells (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (1))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) ) ” 
  &&  “ (RowPrefixIs (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (1))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) v_pre (NodeSlice (arr) (hi_pre) (hi_pre)) (r + 1 ) ) ” 
  &&  “ (CellsShaped (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (1))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) ) ”
  &&  emp
).

Definition build_entail_wit_2_2_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) <> 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr_2 )) (PreH19 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (RowsAgreeExcept v_pre cells (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (1))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) )
.

Definition build_entail_wit_2_2_split_goal_2 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) <> 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr_2 )) (PreH19 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (RowPrefixIs (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (1))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) v_pre (NodeSlice (arr) (hi_pre) (hi_pre)) (r + 1 ) )
.

Definition build_entail_wit_2_2_split_goal_3 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) <> 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr_2 )) (PreH19 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (CellsShaped (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (1))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) )
.

Definition build_entail_wit_3 := 
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (cells1_2: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1_2 )) (PreH2 : (TreeOK cells1_2 arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre )) (PreH3 : (CellsAgreeOutside ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre cells1 cells1_2 )) (PreH4 : (CellsShaped cells1 )) (PreH5 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH6 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH7 : (lo_pre <> hi_pre)) (PreH8 : (NodeFits v_pre lo_pre hi_pre )) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1_2 )
|--
  EX (cells2: (@list (@list (@option Z)))) ,
  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (((lo_pre + hi_pre ) ÷ 2 ) < hi_pre) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (((lo_pre + hi_pre ) ÷ 2 ) = ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (((2 * v_pre ) + 1 ) < 400020) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells2 ) ” 
  &&  “ (TreeOK cells2 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (cells1_2: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1_2 )) (PreH2 : (TreeOK cells1_2 arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre )) (PreH3 : (CellsAgreeOutside ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre cells1 cells1_2 )) (PreH4 : (CellsShaped cells1 )) (PreH5 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH6 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH7 : (lo_pre <> hi_pre)) (PreH8 : (NodeFits v_pre lo_pre hi_pre )) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) ,
  TT && emp 
|--
  “ (CellsAgreeOutside v_pre lo_pre hi_pre cells cells1_2 ) ” 
  &&  “ (TreeOK cells1_2 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ (((2 * v_pre ) + 1 ) < 400020) ” 
  &&  “ (((lo_pre + hi_pre ) ÷ 2 ) < hi_pre) ” 
  &&  “ (lo_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (1 <= lo_pre) ”
  &&  emp
).

Definition build_entail_wit_3_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (cells1_2: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1_2 )) (PreH2 : (TreeOK cells1_2 arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre )) (PreH3 : (CellsAgreeOutside ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre cells1 cells1_2 )) (PreH4 : (CellsShaped cells1 )) (PreH5 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH6 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH7 : (lo_pre <> hi_pre)) (PreH8 : (NodeFits v_pre lo_pre hi_pre )) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) ,
  (CellsAgreeOutside v_pre lo_pre hi_pre cells cells1_2 )
.

Definition build_entail_wit_3_split_goal_2 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (cells1_2: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1_2 )) (PreH2 : (TreeOK cells1_2 arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre )) (PreH3 : (CellsAgreeOutside ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre cells1 cells1_2 )) (PreH4 : (CellsShaped cells1 )) (PreH5 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH6 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH7 : (lo_pre <> hi_pre)) (PreH8 : (NodeFits v_pre lo_pre hi_pre )) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) ,
  (TreeOK cells1_2 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )
.

Definition build_entail_wit_3_split_goal_3 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (cells1_2: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1_2 )) (PreH2 : (TreeOK cells1_2 arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre )) (PreH3 : (CellsAgreeOutside ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre cells1 cells1_2 )) (PreH4 : (CellsShaped cells1 )) (PreH5 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH6 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH7 : (lo_pre <> hi_pre)) (PreH8 : (NodeFits v_pre lo_pre hi_pre )) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) ,
  (((2 * v_pre ) + 1 ) < 400020)
.

Definition build_entail_wit_3_split_goal_4 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (cells1_2: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1_2 )) (PreH2 : (TreeOK cells1_2 arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre )) (PreH3 : (CellsAgreeOutside ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre cells1 cells1_2 )) (PreH4 : (CellsShaped cells1 )) (PreH5 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH6 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH7 : (lo_pre <> hi_pre)) (PreH8 : (NodeFits v_pre lo_pre hi_pre )) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) ,
  (((lo_pre + hi_pre ) ÷ 2 ) < hi_pre)
.

Definition build_entail_wit_3_split_goal_5 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (cells1_2: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1_2 )) (PreH2 : (TreeOK cells1_2 arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre )) (PreH3 : (CellsAgreeOutside ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre cells1 cells1_2 )) (PreH4 : (CellsShaped cells1 )) (PreH5 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH6 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH7 : (lo_pre <> hi_pre)) (PreH8 : (NodeFits v_pre lo_pre hi_pre )) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) ,
  (lo_pre <= ((lo_pre + hi_pre ) ÷ 2 ))
.

Definition build_entail_wit_3_split_goal_6 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (cells1_2: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1_2 )) (PreH2 : (TreeOK cells1_2 arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre )) (PreH3 : (CellsAgreeOutside ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre cells1 cells1_2 )) (PreH4 : (CellsShaped cells1 )) (PreH5 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH6 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH7 : (lo_pre <> hi_pre)) (PreH8 : (NodeFits v_pre lo_pre hi_pre )) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) ,
  (1 <= lo_pre)
.

Definition build_return_wit_1 := 
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (r >= 60)) (PreH2 : (lo_pre = hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= n)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH13 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH14 : (0 <= r)) (PreH15 : (r <= 60)) (PreH16 : (PeriodsOK arr )) (PreH17 : (CellsShaped cellsr )) (PreH18 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH19 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  EX (cells1: (@list (@list (@option Z)))) ,
  “ (CellsShaped cells1 ) ” 
  &&  “ (TreeOK cells1 arr v_pre lo_pre hi_pre ) ” 
  &&  “ (CellsAgreeOutside v_pre lo_pre hi_pre cells cells1 ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (r >= 60)) (PreH2 : (lo_pre = hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= n)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH13 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH14 : (0 <= r)) (PreH15 : (r <= 60)) (PreH16 : (PeriodsOK arr )) (PreH17 : (CellsShaped cellsr )) (PreH18 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH19 : (RowsAgreeExcept v_pre cells cellsr )) ,
  TT && emp 
|--
  “ (CellsAgreeOutside v_pre hi_pre hi_pre cells cellsr ) ” 
  &&  “ (TreeOK cellsr arr v_pre hi_pre hi_pre ) ”
  &&  emp
).

Definition build_return_wit_1_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (r >= 60)) (PreH2 : (lo_pre = hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= n)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH13 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH14 : (0 <= r)) (PreH15 : (r <= 60)) (PreH16 : (PeriodsOK arr )) (PreH17 : (CellsShaped cellsr )) (PreH18 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH19 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (CellsAgreeOutside v_pre hi_pre hi_pre cells cellsr )
.

Definition build_return_wit_1_split_goal_2 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (r >= 60)) (PreH2 : (lo_pre = hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= n)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH13 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH14 : (0 <= r)) (PreH15 : (r <= 60)) (PreH16 : (PeriodsOK arr )) (PreH17 : (CellsShaped cellsr )) (PreH18 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH19 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (TreeOK cellsr arr v_pre hi_pre hi_pre )
.

Definition build_return_wit_2 := 
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (cells1_2: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1_2 )) (PreH2 : (RowIs cells1_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) )) (PreH3 : (RowsAgreeExcept v_pre cells2 cells1_2 )) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= lo_pre)) (PreH6 : (lo_pre <= mid)) (PreH7 : (mid < hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH13 : (((2 * v_pre ) + 1 ) < 400020)) (PreH14 : (PeriodsOK arr )) (PreH15 : (CellsShaped cells2 )) (PreH16 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH17 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH18 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1_2 )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
|--
  EX (cells1: (@list (@list (@option Z)))) ,
  “ (CellsShaped cells1 ) ” 
  &&  “ (TreeOK cells1 arr v_pre lo_pre hi_pre ) ” 
  &&  “ (CellsAgreeOutside v_pre lo_pre hi_pre cells cells1 ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (cells1_2: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1_2 )) (PreH2 : (RowIs cells1_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) )) (PreH3 : (RowsAgreeExcept v_pre cells2 cells1_2 )) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= lo_pre)) (PreH6 : (lo_pre <= mid)) (PreH7 : (mid < hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH13 : (((2 * v_pre ) + 1 ) < 400020)) (PreH14 : (PeriodsOK arr )) (PreH15 : (CellsShaped cells2 )) (PreH16 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH17 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH18 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  TT && emp 
|--
  “ (CellsAgreeOutside v_pre lo_pre hi_pre cells cells1_2 ) ” 
  &&  “ (TreeOK cells1_2 arr v_pre lo_pre hi_pre ) ”
  &&  emp
).

Definition build_return_wit_2_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (cells1_2: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1_2 )) (PreH2 : (RowIs cells1_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) )) (PreH3 : (RowsAgreeExcept v_pre cells2 cells1_2 )) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= lo_pre)) (PreH6 : (lo_pre <= mid)) (PreH7 : (mid < hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH13 : (((2 * v_pre ) + 1 ) < 400020)) (PreH14 : (PeriodsOK arr )) (PreH15 : (CellsShaped cells2 )) (PreH16 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH17 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH18 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  (CellsAgreeOutside v_pre lo_pre hi_pre cells cells1_2 )
.

Definition build_return_wit_2_split_goal_2 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (cells1_2: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1_2 )) (PreH2 : (RowIs cells1_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) )) (PreH3 : (RowsAgreeExcept v_pre cells2 cells1_2 )) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= lo_pre)) (PreH6 : (lo_pre <= mid)) (PreH7 : (mid < hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH13 : (((2 * v_pre ) + 1 ) < 400020)) (PreH14 : (PeriodsOK arr )) (PreH15 : (CellsShaped cells2 )) (PreH16 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH17 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH18 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  (TreeOK cells1_2 arr v_pre lo_pre hi_pre )
.

Definition build_partial_solve_wit_1 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (r < 60)) (PreH2 : (lo_pre = hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= n)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH13 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH14 : (0 <= r)) (PreH15 : (r <= 60)) (PreH16 : (PeriodsOK arr )) (PreH17 : (CellsShaped cellsr )) (PreH18 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH19 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (r < 60) ” 
  &&  “ (lo_pre = hi_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= n) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (2 <= (Znth ((lo_pre - 1 )) (arr) (0))) ” 
  &&  “ ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r <= 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cellsr ) ” 
  &&  “ (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r ) ” 
  &&  “ (RowsAgreeExcept v_pre cells cellsr ) ”
  &&  (((( &( "a_" ) ) + (lo_pre * sizeof(INT)))) # Int  |-> (Znth (lo_pre - 1 ) arr 0))
  **  (IntArray.missing_i ( &( "a_" ) ) lo_pre 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
.

Definition build_partial_solve_wit_2 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) = 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) = 0) ” 
  &&  “ (r < 60) ” 
  &&  “ (lo_pre = hi_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= n) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (2 <= (Znth ((lo_pre - 1 )) (arr) (0))) ” 
  &&  “ ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r <= 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cellsr ) ” 
  &&  “ (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r ) ” 
  &&  “ (RowsAgreeExcept v_pre cells cellsr ) ”
  &&  ((((( &( "seg" ) ) + (v_pre * (sizeof(INT) * 60))) + (r * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i (( &( "seg" ) ) + (v_pre * (sizeof(INT) * 60))) r 0 60 (Znth v_pre cellsr __default__List__App_option_Z) )
  **  (IntArray2.mixed_missing_i ( &( "seg" ) ) v_pre 0 400020 60 cellsr )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
.

Definition build_partial_solve_wit_3 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) <> 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) <> 0) ” 
  &&  “ (r < 60) ” 
  &&  “ (lo_pre = hi_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= n) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (2 <= (Znth ((lo_pre - 1 )) (arr) (0))) ” 
  &&  “ ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r <= 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cellsr ) ” 
  &&  “ (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r ) ” 
  &&  “ (RowsAgreeExcept v_pre cells cellsr ) ”
  &&  ((((( &( "seg" ) ) + (v_pre * (sizeof(INT) * 60))) + (r * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i (( &( "seg" ) ) + (v_pre * (sizeof(INT) * 60))) r 0 60 (Znth v_pre cellsr __default__List__App_option_Z) )
  **  (IntArray2.mixed_missing_i ( &( "seg" ) ) v_pre 0 400020 60 cellsr )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
.

Definition build_partial_solve_wit_4_pure := 
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (((lo_pre + hi_pre ) ÷ 2 ) <= n) ” 
  &&  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ”
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (hi_pre <= INT_MAX)) (PreH2 : (lo_pre <= INT_MAX)) (PreH3 : (v_pre <= INT_MAX)) (PreH4 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH5 : (hi_pre >= INT_MIN)) (PreH6 : (lo_pre >= INT_MIN)) (PreH7 : (v_pre >= INT_MIN)) (PreH8 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH9 : (lo_pre <> hi_pre)) (PreH10 : (NodeFits v_pre lo_pre hi_pre )) (PreH11 : (hi_pre <= n)) (PreH12 : (n = (Zlength (arr)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 100000)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cells )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ (((lo_pre + hi_pre ) ÷ 2 ) <= n) ”
).

Definition build_partial_solve_wit_4_pure_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (hi_pre <= INT_MAX)) (PreH2 : (lo_pre <= INT_MAX)) (PreH3 : (v_pre <= INT_MAX)) (PreH4 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH5 : (hi_pre >= INT_MIN)) (PreH6 : (lo_pre >= INT_MIN)) (PreH7 : (v_pre >= INT_MIN)) (PreH8 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH9 : (lo_pre <> hi_pre)) (PreH10 : (NodeFits v_pre lo_pre hi_pre )) (PreH11 : (hi_pre <= n)) (PreH12 : (n = (Zlength (arr)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 100000)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cells )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ”
.

Definition build_partial_solve_wit_4_pure_split_goal_2 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (hi_pre <= INT_MAX)) (PreH2 : (lo_pre <= INT_MAX)) (PreH3 : (v_pre <= INT_MAX)) (PreH4 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH5 : (hi_pre >= INT_MIN)) (PreH6 : (lo_pre >= INT_MIN)) (PreH7 : (v_pre >= INT_MIN)) (PreH8 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH9 : (lo_pre <> hi_pre)) (PreH10 : (NodeFits v_pre lo_pre hi_pre )) (PreH11 : (hi_pre <= n)) (PreH12 : (n = (Zlength (arr)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 100000)) (PreH15 : (PeriodsOK arr )) (PreH16 : (CellsShaped cells )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (((lo_pre + hi_pre ) ÷ 2 ) <= n) ”
.

Definition build_partial_solve_wit_4_aux := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (PeriodsOK arr )) (PreH8 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (((lo_pre + hi_pre ) ÷ 2 ) <= n) ” 
  &&  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ (lo_pre <> hi_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
.

Definition build_partial_solve_wit_4 := build_partial_solve_wit_4_pure -> build_partial_solve_wit_4_aux.

Definition build_partial_solve_wit_5_pure := 
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (lo_pre <> hi_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (hi_pre <= n)) (PreH7 : (n = (Zlength (arr)))) (PreH8 : (1 <= n)) (PreH9 : (n <= 100000)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells1 ) ” 
  &&  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (hi_pre <= INT_MAX)) (PreH2 : (lo_pre <= INT_MAX)) (PreH3 : (v_pre <= INT_MAX)) (PreH4 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH5 : (hi_pre >= INT_MIN)) (PreH6 : (lo_pre >= INT_MIN)) (PreH7 : (v_pre >= INT_MIN)) (PreH8 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH9 : (CellsShaped cells1 )) (PreH10 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH11 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH12 : (lo_pre <> hi_pre)) (PreH13 : (NodeFits v_pre lo_pre hi_pre )) (PreH14 : (hi_pre <= n)) (PreH15 : (n = (Zlength (arr)))) (PreH16 : (1 <= n)) (PreH17 : (n <= 100000)) (PreH18 : (PeriodsOK arr )) (PreH19 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
).

Definition build_partial_solve_wit_5_pure_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (hi_pre <= INT_MAX)) (PreH2 : (lo_pre <= INT_MAX)) (PreH3 : (v_pre <= INT_MAX)) (PreH4 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH5 : (hi_pre >= INT_MIN)) (PreH6 : (lo_pre >= INT_MIN)) (PreH7 : (v_pre >= INT_MIN)) (PreH8 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH9 : (CellsShaped cells1 )) (PreH10 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH11 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH12 : (lo_pre <> hi_pre)) (PreH13 : (NodeFits v_pre lo_pre hi_pre )) (PreH14 : (hi_pre <= n)) (PreH15 : (n = (Zlength (arr)))) (PreH16 : (1 <= n)) (PreH17 : (n <= 100000)) (PreH18 : (PeriodsOK arr )) (PreH19 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
.

Definition build_partial_solve_wit_5_aux := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (lo_pre <> hi_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (hi_pre <= n)) (PreH7 : (n = (Zlength (arr)))) (PreH8 : (1 <= n)) (PreH9 : (n <= 100000)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
|--
  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells1 ) ” 
  &&  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ (CellsShaped cells1 ) ” 
  &&  “ (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 ) ” 
  &&  “ (lo_pre <> hi_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
.

Definition build_partial_solve_wit_5 := build_partial_solve_wit_5_pure -> build_partial_solve_wit_5_aux.

Definition build_partial_solve_wit_6_pure := 
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (PreH1 : (NodeFits v_pre lo_pre hi_pre )) (PreH2 : (1 <= lo_pre)) (PreH3 : (lo_pre <= mid)) (PreH4 : (mid < hi_pre)) (PreH5 : (hi_pre <= n)) (PreH6 : (n = (Zlength (arr)))) (PreH7 : (1 <= n)) (PreH8 : (n <= 100000)) (PreH9 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH10 : (((2 * v_pre ) + 1 ) < 400020)) (PreH11 : (PeriodsOK arr )) (PreH12 : (CellsShaped cells2 )) (PreH13 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH14 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH15 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
|--
  “ (((2 * v_pre ) + 1 ) < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= mid) ” 
  &&  “ (mid < hi_pre) ” 
  &&  “ (hi_pre <= (Zlength (arr))) ” 
  &&  “ ((Zlength (arr)) <= 100000) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells2 ) ” 
  &&  “ (RowIs cells2 (2 * v_pre ) (NodeSlice (arr) (lo_pre) (mid)) ) ” 
  &&  “ (RowIs cells2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi_pre)) ) ” 
  &&  “ (RowIs cells2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre)) ) ” 
  &&  “ (RowIs cells2 (2 * v_pre ) (NodeSlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 ))) ) ” 
  &&  “ (1 <= v_pre) ”
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (PreH1 : (mid <= INT_MAX)) (PreH2 : (hi_pre <= INT_MAX)) (PreH3 : (lo_pre <= INT_MAX)) (PreH4 : (v_pre <= INT_MAX)) (PreH5 : (mid >= INT_MIN)) (PreH6 : (hi_pre >= INT_MIN)) (PreH7 : (lo_pre >= INT_MIN)) (PreH8 : (v_pre >= INT_MIN)) (PreH9 : (NodeFits v_pre lo_pre hi_pre )) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= mid)) (PreH12 : (mid < hi_pre)) (PreH13 : (hi_pre <= n)) (PreH14 : (n = (Zlength (arr)))) (PreH15 : (1 <= n)) (PreH16 : (n <= 100000)) (PreH17 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH18 : (((2 * v_pre ) + 1 ) < 400020)) (PreH19 : (PeriodsOK arr )) (PreH20 : (CellsShaped cells2 )) (PreH21 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH22 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH23 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
|--
  “ (1 <= v_pre) ” 
  &&  “ (RowIs cells2 (2 * v_pre ) (NodeSlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 ))) ) ” 
  &&  “ (RowIs cells2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre)) ) ” 
  &&  “ (RowIs cells2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre)) ) ” 
  &&  “ (RowIs cells2 (2 * v_pre ) (NodeSlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 ))) ) ”
).

Definition build_partial_solve_wit_6_pure_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (PreH1 : (mid <= INT_MAX)) (PreH2 : (hi_pre <= INT_MAX)) (PreH3 : (lo_pre <= INT_MAX)) (PreH4 : (v_pre <= INT_MAX)) (PreH5 : (mid >= INT_MIN)) (PreH6 : (hi_pre >= INT_MIN)) (PreH7 : (lo_pre >= INT_MIN)) (PreH8 : (v_pre >= INT_MIN)) (PreH9 : (NodeFits v_pre lo_pre hi_pre )) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= mid)) (PreH12 : (mid < hi_pre)) (PreH13 : (hi_pre <= n)) (PreH14 : (n = (Zlength (arr)))) (PreH15 : (1 <= n)) (PreH16 : (n <= 100000)) (PreH17 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH18 : (((2 * v_pre ) + 1 ) < 400020)) (PreH19 : (PeriodsOK arr )) (PreH20 : (CellsShaped cells2 )) (PreH21 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH22 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH23 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
|--
  “ (1 <= v_pre) ”
.

Definition build_partial_solve_wit_6_pure_split_goal_2 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (PreH1 : (mid <= INT_MAX)) (PreH2 : (hi_pre <= INT_MAX)) (PreH3 : (lo_pre <= INT_MAX)) (PreH4 : (v_pre <= INT_MAX)) (PreH5 : (mid >= INT_MIN)) (PreH6 : (hi_pre >= INT_MIN)) (PreH7 : (lo_pre >= INT_MIN)) (PreH8 : (v_pre >= INT_MIN)) (PreH9 : (NodeFits v_pre lo_pre hi_pre )) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= mid)) (PreH12 : (mid < hi_pre)) (PreH13 : (hi_pre <= n)) (PreH14 : (n = (Zlength (arr)))) (PreH15 : (1 <= n)) (PreH16 : (n <= 100000)) (PreH17 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH18 : (((2 * v_pre ) + 1 ) < 400020)) (PreH19 : (PeriodsOK arr )) (PreH20 : (CellsShaped cells2 )) (PreH21 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH22 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH23 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
|--
  “ (RowIs cells2 (2 * v_pre ) (NodeSlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 ))) ) ”
.

Definition build_partial_solve_wit_6_pure_split_goal_3 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (PreH1 : (mid <= INT_MAX)) (PreH2 : (hi_pre <= INT_MAX)) (PreH3 : (lo_pre <= INT_MAX)) (PreH4 : (v_pre <= INT_MAX)) (PreH5 : (mid >= INT_MIN)) (PreH6 : (hi_pre >= INT_MIN)) (PreH7 : (lo_pre >= INT_MIN)) (PreH8 : (v_pre >= INT_MIN)) (PreH9 : (NodeFits v_pre lo_pre hi_pre )) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= mid)) (PreH12 : (mid < hi_pre)) (PreH13 : (hi_pre <= n)) (PreH14 : (n = (Zlength (arr)))) (PreH15 : (1 <= n)) (PreH16 : (n <= 100000)) (PreH17 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH18 : (((2 * v_pre ) + 1 ) < 400020)) (PreH19 : (PeriodsOK arr )) (PreH20 : (CellsShaped cells2 )) (PreH21 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH22 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH23 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
|--
  “ (RowIs cells2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre)) ) ”
.

Definition build_partial_solve_wit_6_pure_split_goal_4 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (PreH1 : (mid <= INT_MAX)) (PreH2 : (hi_pre <= INT_MAX)) (PreH3 : (lo_pre <= INT_MAX)) (PreH4 : (v_pre <= INT_MAX)) (PreH5 : (mid >= INT_MIN)) (PreH6 : (hi_pre >= INT_MIN)) (PreH7 : (lo_pre >= INT_MIN)) (PreH8 : (v_pre >= INT_MIN)) (PreH9 : (NodeFits v_pre lo_pre hi_pre )) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= mid)) (PreH12 : (mid < hi_pre)) (PreH13 : (hi_pre <= n)) (PreH14 : (n = (Zlength (arr)))) (PreH15 : (1 <= n)) (PreH16 : (n <= 100000)) (PreH17 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH18 : (((2 * v_pre ) + 1 ) < 400020)) (PreH19 : (PeriodsOK arr )) (PreH20 : (CellsShaped cells2 )) (PreH21 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH22 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH23 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
|--
  “ (RowIs cells2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre)) ) ”
.

Definition build_partial_solve_wit_6_pure_split_goal_5 := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (PreH1 : (mid <= INT_MAX)) (PreH2 : (hi_pre <= INT_MAX)) (PreH3 : (lo_pre <= INT_MAX)) (PreH4 : (v_pre <= INT_MAX)) (PreH5 : (mid >= INT_MIN)) (PreH6 : (hi_pre >= INT_MIN)) (PreH7 : (lo_pre >= INT_MIN)) (PreH8 : (v_pre >= INT_MIN)) (PreH9 : (NodeFits v_pre lo_pre hi_pre )) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= mid)) (PreH12 : (mid < hi_pre)) (PreH13 : (hi_pre <= n)) (PreH14 : (n = (Zlength (arr)))) (PreH15 : (1 <= n)) (PreH16 : (n <= 100000)) (PreH17 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH18 : (((2 * v_pre ) + 1 ) < 400020)) (PreH19 : (PeriodsOK arr )) (PreH20 : (CellsShaped cells2 )) (PreH21 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH22 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH23 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
|--
  “ (RowIs cells2 (2 * v_pre ) (NodeSlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 ))) ) ”
.

Definition build_partial_solve_wit_6_aux := 
forall (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (PreH1 : (NodeFits v_pre lo_pre hi_pre )) (PreH2 : (1 <= lo_pre)) (PreH3 : (lo_pre <= mid)) (PreH4 : (mid < hi_pre)) (PreH5 : (hi_pre <= n)) (PreH6 : (n = (Zlength (arr)))) (PreH7 : (1 <= n)) (PreH8 : (n <= 100000)) (PreH9 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH10 : (((2 * v_pre ) + 1 ) < 400020)) (PreH11 : (PeriodsOK arr )) (PreH12 : (CellsShaped cells2 )) (PreH13 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH14 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH15 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
|--
  “ (((2 * v_pre ) + 1 ) < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= mid) ” 
  &&  “ (mid < hi_pre) ” 
  &&  “ (hi_pre <= (Zlength (arr))) ” 
  &&  “ ((Zlength (arr)) <= 100000) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells2 ) ” 
  &&  “ (RowIs cells2 (2 * v_pre ) (NodeSlice (arr) (lo_pre) (mid)) ) ” 
  &&  “ (RowIs cells2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi_pre)) ) ” 
  &&  “ (RowIs cells2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre)) ) ” 
  &&  “ (RowIs cells2 (2 * v_pre ) (NodeSlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 ))) ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= mid) ” 
  &&  “ (mid < hi_pre) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (mid = ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (((2 * v_pre ) + 1 ) < 400020) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells2 ) ” 
  &&  “ (TreeOK cells2 arr (2 * v_pre ) lo_pre mid ) ” 
  &&  “ (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre ) ” 
  &&  “ (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 ) ”
  &&  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
.

Definition build_partial_solve_wit_6 := build_partial_solve_wit_6_pure -> build_partial_solve_wit_6_aux.

(*----- Function update -----*)

Definition update_safety_wit_1 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (lo_pre <= pos_pre)) (PreH8 : (pos_pre <= hi_pre)) (PreH9 : (PeriodsOK arr )) (PreH10 : (CellsShaped cells )) (PreH11 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition update_safety_wit_2 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (lo_pre = pos_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= n)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH13 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH14 : (0 <= r)) (PreH15 : (r <= 60)) (PreH16 : (PeriodsOK arr )) (PreH17 : (CellsShaped cellsr )) (PreH18 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH19 : (RowsAgreeExcept v_pre cells cellsr )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (60 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 60) ”
.

Definition update_safety_wit_3 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) = 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (lo_pre = pos_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= n)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH15 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH16 : (0 <= r)) (PreH17 : (r <= 60)) (PreH18 : (PeriodsOK arr )) (PreH19 : (CellsShaped cellsr )) (PreH20 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH21 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (2))) ((Znth v_pre cellsr __default__List__App_option_Z)))) (cellsr)) )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ ((r + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition update_safety_wit_4 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) <> 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (lo_pre = pos_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= n)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH15 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH16 : (0 <= r)) (PreH17 : (r <= 60)) (PreH18 : (PeriodsOK arr )) (PreH19 : (CellsShaped cellsr )) (PreH20 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH21 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (1))) ((Znth v_pre cellsr __default__List__App_option_Z)))) (cellsr)) )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
|--
  “ ((r + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition update_safety_wit_5 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (r < 60)) (PreH2 : (lo_pre = hi_pre)) (PreH3 : (lo_pre = pos_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ ((r <> (INT_MIN)) \/ ((Znth (lo_pre - 1 ) arr 0) <> (-1))) ” 
  &&  “ ((Znth (lo_pre - 1 ) arr 0) <> 0) ”
.

Definition update_safety_wit_6 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (r < 60)) (PreH2 : (lo_pre = hi_pre)) (PreH3 : (lo_pre = pos_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition update_safety_wit_7 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) = 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (lo_pre = pos_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= n)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH15 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH16 : (0 <= r)) (PreH17 : (r <= 60)) (PreH18 : (PeriodsOK arr )) (PreH19 : (CellsShaped cellsr )) (PreH20 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH21 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition update_safety_wit_8 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) <> 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (lo_pre = pos_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= n)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH15 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH16 : (0 <= r)) (PreH17 : (r <= 60)) (PreH18 : (PeriodsOK arr )) (PreH19 : (CellsShaped cellsr )) (PreH20 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH21 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition update_safety_wit_9 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (lo_pre <= pos_pre)) (PreH8 : (pos_pre <= hi_pre)) (PreH9 : (PeriodsOK arr )) (PreH10 : (CellsShaped cells )) (PreH11 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (((lo_pre + hi_pre ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition update_safety_wit_10 := 
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (lo_pre <= pos_pre)) (PreH8 : (pos_pre <= hi_pre)) (PreH9 : (PeriodsOK arr )) (PreH10 : (CellsShaped cells )) (PreH11 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((lo_pre + hi_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lo_pre + hi_pre )) ”
) \/
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (lo_pre <= pos_pre)) (PreH8 : (pos_pre <= hi_pre)) (PreH9 : (PeriodsOK arr )) (PreH10 : (CellsShaped cells )) (PreH11 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((lo_pre + hi_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lo_pre + hi_pre )) ”
).

Definition update_safety_wit_10_split_goal_1 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (lo_pre <= pos_pre)) (PreH8 : (pos_pre <= hi_pre)) (PreH9 : (PeriodsOK arr )) (PreH10 : (CellsShaped cells )) (PreH11 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((lo_pre + hi_pre ) <= INT_MAX) ”
.

Definition update_safety_wit_10_split_goal_2 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (lo_pre <= pos_pre)) (PreH8 : (pos_pre <= hi_pre)) (PreH9 : (PeriodsOK arr )) (PreH10 : (CellsShaped cells )) (PreH11 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((INT_MIN) <= (lo_pre + hi_pre )) ”
.

Definition update_safety_wit_11 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (lo_pre <= pos_pre)) (PreH8 : (pos_pre <= hi_pre)) (PreH9 : (PeriodsOK arr )) (PreH10 : (CellsShaped cells )) (PreH11 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition update_safety_wit_12 := 
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((2 * v_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * v_pre )) ”
) \/
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((2 * v_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * v_pre )) ”
).

Definition update_safety_wit_12_split_goal_1 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((2 * v_pre ) <= INT_MAX) ”
.

Definition update_safety_wit_12_split_goal_2 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((INT_MIN) <= (2 * v_pre )) ”
.

Definition update_safety_wit_13 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition update_safety_wit_14 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((((lo_pre + hi_pre ) ÷ 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((lo_pre + hi_pre ) ÷ 2 ) + 1 )) ”
.

Definition update_safety_wit_15 := 
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (((2 * v_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * v_pre ) + 1 )) ”
) \/
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (((2 * v_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * v_pre ) + 1 )) ”
).

Definition update_safety_wit_15_split_goal_1 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (((2 * v_pre ) + 1 ) <= INT_MAX) ”
.

Definition update_safety_wit_15_split_goal_2 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((INT_MIN) <= ((2 * v_pre ) + 1 )) ”
.

Definition update_safety_wit_16 := 
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((2 * v_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * v_pre )) ”
) \/
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((2 * v_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * v_pre )) ”
).

Definition update_safety_wit_16_split_goal_1 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((2 * v_pre ) <= INT_MAX) ”
.

Definition update_safety_wit_16_split_goal_2 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((INT_MIN) <= (2 * v_pre )) ”
.

Definition update_safety_wit_17 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition update_safety_wit_18 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition update_safety_wit_19 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition update_entail_wit_1 := 
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (lo_pre <= pos_pre)) (PreH8 : (pos_pre <= hi_pre)) (PreH9 : (PeriodsOK arr )) (PreH10 : (CellsShaped cells )) (PreH11 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  EX (cellsr: (@list (@list (@option Z)))) ,
  “ (lo_pre = hi_pre) ” 
  &&  “ (lo_pre = pos_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= n) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (2 <= (Znth ((lo_pre - 1 )) (arr) (0))) ” 
  &&  “ ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cellsr ) ” 
  &&  “ (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) 0 ) ” 
  &&  “ (RowsAgreeExcept v_pre cells cellsr ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
) \/
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (lo_pre <= pos_pre)) (PreH8 : (pos_pre <= hi_pre)) (PreH9 : (PeriodsOK arr )) (PreH10 : (CellsShaped cells )) (PreH11 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  TT && emp 
|--
  “ (RowsAgreeExcept v_pre cells cells ) ” 
  &&  “ (RowPrefixIs cells v_pre (NodeSlice (arr) (hi_pre) (hi_pre)) 0 ) ” 
  &&  “ ((Znth ((hi_pre - 1 )) (arr) (0)) <= 6) ” 
  &&  “ (2 <= (Znth ((hi_pre - 1 )) (arr) (0))) ” 
  &&  “ (1 <= hi_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= v_pre) ”
  &&  emp
).

Definition update_entail_wit_1_split_goal_1 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (lo_pre <= pos_pre)) (PreH8 : (pos_pre <= hi_pre)) (PreH9 : (PeriodsOK arr )) (PreH10 : (CellsShaped cells )) (PreH11 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (RowsAgreeExcept v_pre cells cells )
.

Definition update_entail_wit_1_split_goal_2 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (lo_pre <= pos_pre)) (PreH8 : (pos_pre <= hi_pre)) (PreH9 : (PeriodsOK arr )) (PreH10 : (CellsShaped cells )) (PreH11 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (RowPrefixIs cells v_pre (NodeSlice (arr) (hi_pre) (hi_pre)) 0 )
.

Definition update_entail_wit_1_split_goal_3 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (lo_pre <= pos_pre)) (PreH8 : (pos_pre <= hi_pre)) (PreH9 : (PeriodsOK arr )) (PreH10 : (CellsShaped cells )) (PreH11 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((Znth ((hi_pre - 1 )) (arr) (0)) <= 6)
.

Definition update_entail_wit_1_split_goal_4 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (lo_pre <= pos_pre)) (PreH8 : (pos_pre <= hi_pre)) (PreH9 : (PeriodsOK arr )) (PreH10 : (CellsShaped cells )) (PreH11 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (2 <= (Znth ((hi_pre - 1 )) (arr) (0)))
.

Definition update_entail_wit_1_split_goal_5 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (lo_pre <= pos_pre)) (PreH8 : (pos_pre <= hi_pre)) (PreH9 : (PeriodsOK arr )) (PreH10 : (CellsShaped cells )) (PreH11 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (1 <= hi_pre)
.

Definition update_entail_wit_1_split_goal_6 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (lo_pre <= pos_pre)) (PreH8 : (pos_pre <= hi_pre)) (PreH9 : (PeriodsOK arr )) (PreH10 : (CellsShaped cells )) (PreH11 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (v_pre < 400020)
.

Definition update_entail_wit_1_split_goal_7 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (hi_pre <= n)) (PreH4 : (n = (Zlength (arr)))) (PreH5 : (1 <= n)) (PreH6 : (n <= 100000)) (PreH7 : (lo_pre <= pos_pre)) (PreH8 : (pos_pre <= hi_pre)) (PreH9 : (PeriodsOK arr )) (PreH10 : (CellsShaped cells )) (PreH11 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (1 <= v_pre)
.

Definition update_entail_wit_2_1 := 
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) = 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (lo_pre = pos_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= n)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH15 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH16 : (0 <= r)) (PreH17 : (r <= 60)) (PreH18 : (PeriodsOK arr )) (PreH19 : (CellsShaped cellsr_2 )) (PreH20 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH21 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (2))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
|--
  EX (cellsr: (@list (@list (@option Z)))) ,
  “ (lo_pre = hi_pre) ” 
  &&  “ (lo_pre = pos_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= n) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (2 <= (Znth ((lo_pre - 1 )) (arr) (0))) ” 
  &&  “ ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6) ” 
  &&  “ (0 <= (r + 1 )) ” 
  &&  “ ((r + 1 ) <= 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cellsr ) ” 
  &&  “ (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) (r + 1 ) ) ” 
  &&  “ (RowsAgreeExcept v_pre cells cellsr ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
) \/
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) = 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (lo_pre = pos_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= n)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH15 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH16 : (0 <= r)) (PreH17 : (r <= 60)) (PreH18 : (PeriodsOK arr )) (PreH19 : (CellsShaped cellsr_2 )) (PreH20 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH21 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  TT && emp 
|--
  “ (RowsAgreeExcept v_pre cells (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (2))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) ) ” 
  &&  “ (RowPrefixIs (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (2))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) v_pre (NodeSlice (arr) (hi_pre) (hi_pre)) (r + 1 ) ) ” 
  &&  “ (CellsShaped (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (2))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) ) ”
  &&  emp
).

Definition update_entail_wit_2_1_split_goal_1 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) = 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (lo_pre = pos_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= n)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH15 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH16 : (0 <= r)) (PreH17 : (r <= 60)) (PreH18 : (PeriodsOK arr )) (PreH19 : (CellsShaped cellsr_2 )) (PreH20 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH21 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (RowsAgreeExcept v_pre cells (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (2))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) )
.

Definition update_entail_wit_2_1_split_goal_2 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) = 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (lo_pre = pos_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= n)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH15 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH16 : (0 <= r)) (PreH17 : (r <= 60)) (PreH18 : (PeriodsOK arr )) (PreH19 : (CellsShaped cellsr_2 )) (PreH20 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH21 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (RowPrefixIs (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (2))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) v_pre (NodeSlice (arr) (hi_pre) (hi_pre)) (r + 1 ) )
.

Definition update_entail_wit_2_1_split_goal_3 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) = 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (lo_pre = pos_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= n)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH15 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH16 : (0 <= r)) (PreH17 : (r <= 60)) (PreH18 : (PeriodsOK arr )) (PreH19 : (CellsShaped cellsr_2 )) (PreH20 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH21 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (CellsShaped (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (2))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) )
.

Definition update_entail_wit_2_2 := 
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) <> 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (lo_pre = pos_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= n)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH15 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH16 : (0 <= r)) (PreH17 : (r <= 60)) (PreH18 : (PeriodsOK arr )) (PreH19 : (CellsShaped cellsr_2 )) (PreH20 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH21 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (1))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
|--
  EX (cellsr: (@list (@list (@option Z)))) ,
  “ (lo_pre = hi_pre) ” 
  &&  “ (lo_pre = pos_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= n) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (2 <= (Znth ((lo_pre - 1 )) (arr) (0))) ” 
  &&  “ ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6) ” 
  &&  “ (0 <= (r + 1 )) ” 
  &&  “ ((r + 1 ) <= 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cellsr ) ” 
  &&  “ (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) (r + 1 ) ) ” 
  &&  “ (RowsAgreeExcept v_pre cells cellsr ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
) \/
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) <> 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (lo_pre = pos_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= n)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH15 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH16 : (0 <= r)) (PreH17 : (r <= 60)) (PreH18 : (PeriodsOK arr )) (PreH19 : (CellsShaped cellsr_2 )) (PreH20 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH21 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  TT && emp 
|--
  “ (RowsAgreeExcept v_pre cells (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (1))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) ) ” 
  &&  “ (RowPrefixIs (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (1))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) v_pre (NodeSlice (arr) (hi_pre) (hi_pre)) (r + 1 ) ) ” 
  &&  “ (CellsShaped (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (1))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) ) ”
  &&  emp
).

Definition update_entail_wit_2_2_split_goal_1 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) <> 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (lo_pre = pos_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= n)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH15 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH16 : (0 <= r)) (PreH17 : (r <= 60)) (PreH18 : (PeriodsOK arr )) (PreH19 : (CellsShaped cellsr_2 )) (PreH20 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH21 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (RowsAgreeExcept v_pre cells (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (1))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) )
.

Definition update_entail_wit_2_2_split_goal_2 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) <> 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (lo_pre = pos_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= n)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH15 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH16 : (0 <= r)) (PreH17 : (r <= 60)) (PreH18 : (PeriodsOK arr )) (PreH19 : (CellsShaped cellsr_2 )) (PreH20 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH21 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (RowPrefixIs (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (1))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) v_pre (NodeSlice (arr) (hi_pre) (hi_pre)) (r + 1 ) )
.

Definition update_entail_wit_2_2_split_goal_3 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr_2: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) <> 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (lo_pre = pos_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= n)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH15 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH16 : (0 <= r)) (PreH17 : (r <= 60)) (PreH18 : (PeriodsOK arr )) (PreH19 : (CellsShaped cellsr_2 )) (PreH20 : (RowPrefixIs cellsr_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH21 : (RowsAgreeExcept v_pre cells cellsr_2 )) ,
  (CellsShaped (Array2.replace_mixed_row (v_pre) ((replace_Znth (r) ((Some (1))) ((Znth v_pre cellsr_2 __default__List__App_option_Z)))) (cellsr_2)) )
.

Definition update_entail_wit_3_1 := 
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (lo_pre <> hi_pre)) (PreH6 : (NodeFits v_pre lo_pre hi_pre )) (PreH7 : (hi_pre <= n)) (PreH8 : (n = (Zlength (arr)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 100000)) (PreH11 : (lo_pre <= pos_pre)) (PreH12 : (pos_pre <= hi_pre)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
|--
  EX (cells2: (@list (@list (@option Z)))) ,
  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (((lo_pre + hi_pre ) ÷ 2 ) < hi_pre) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (((lo_pre + hi_pre ) ÷ 2 ) = ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (lo_pre <= pos_pre) ” 
  &&  “ (pos_pre <= hi_pre) ” 
  &&  “ (((2 * v_pre ) + 1 ) < 400020) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells2 ) ” 
  &&  “ (TreeOK cells2 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
) \/
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (lo_pre <> hi_pre)) (PreH6 : (NodeFits v_pre lo_pre hi_pre )) (PreH7 : (hi_pre <= n)) (PreH8 : (n = (Zlength (arr)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 100000)) (PreH11 : (lo_pre <= pos_pre)) (PreH12 : (pos_pre <= hi_pre)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  TT && emp 
|--
  “ (CellsAgreeOutside v_pre lo_pre hi_pre cells cells1 ) ” 
  &&  “ (TreeOK cells1 arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ (((2 * v_pre ) + 1 ) < 400020) ” 
  &&  “ (((lo_pre + hi_pre ) ÷ 2 ) < hi_pre) ” 
  &&  “ (1 <= lo_pre) ”
  &&  emp
).

Definition update_entail_wit_3_1_split_goal_1 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (lo_pre <> hi_pre)) (PreH6 : (NodeFits v_pre lo_pre hi_pre )) (PreH7 : (hi_pre <= n)) (PreH8 : (n = (Zlength (arr)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 100000)) (PreH11 : (lo_pre <= pos_pre)) (PreH12 : (pos_pre <= hi_pre)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (CellsAgreeOutside v_pre lo_pre hi_pre cells cells1 )
.

Definition update_entail_wit_3_1_split_goal_2 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (lo_pre <> hi_pre)) (PreH6 : (NodeFits v_pre lo_pre hi_pre )) (PreH7 : (hi_pre <= n)) (PreH8 : (n = (Zlength (arr)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 100000)) (PreH11 : (lo_pre <= pos_pre)) (PreH12 : (pos_pre <= hi_pre)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (TreeOK cells1 arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre )
.

Definition update_entail_wit_3_1_split_goal_3 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (lo_pre <> hi_pre)) (PreH6 : (NodeFits v_pre lo_pre hi_pre )) (PreH7 : (hi_pre <= n)) (PreH8 : (n = (Zlength (arr)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 100000)) (PreH11 : (lo_pre <= pos_pre)) (PreH12 : (pos_pre <= hi_pre)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (((2 * v_pre ) + 1 ) < 400020)
.

Definition update_entail_wit_3_1_split_goal_4 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (lo_pre <> hi_pre)) (PreH6 : (NodeFits v_pre lo_pre hi_pre )) (PreH7 : (hi_pre <= n)) (PreH8 : (n = (Zlength (arr)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 100000)) (PreH11 : (lo_pre <= pos_pre)) (PreH12 : (pos_pre <= hi_pre)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (((lo_pre + hi_pre ) ÷ 2 ) < hi_pre)
.

Definition update_entail_wit_3_1_split_goal_5 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )) (PreH3 : (CellsAgreeOutside (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) cells cells1 )) (PreH4 : (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (lo_pre <> hi_pre)) (PreH6 : (NodeFits v_pre lo_pre hi_pre )) (PreH7 : (hi_pre <= n)) (PreH8 : (n = (Zlength (arr)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 100000)) (PreH11 : (lo_pre <= pos_pre)) (PreH12 : (pos_pre <= hi_pre)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (1 <= lo_pre)
.

Definition update_entail_wit_3_2 := 
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre )) (PreH3 : (CellsAgreeOutside ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre cells cells1 )) (PreH4 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (lo_pre <> hi_pre)) (PreH6 : (NodeFits v_pre lo_pre hi_pre )) (PreH7 : (hi_pre <= n)) (PreH8 : (n = (Zlength (arr)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 100000)) (PreH11 : (lo_pre <= pos_pre)) (PreH12 : (pos_pre <= hi_pre)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
|--
  EX (cells2: (@list (@list (@option Z)))) ,
  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (((lo_pre + hi_pre ) ÷ 2 ) < hi_pre) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (((lo_pre + hi_pre ) ÷ 2 ) = ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (lo_pre <= pos_pre) ” 
  &&  “ (pos_pre <= hi_pre) ” 
  &&  “ (((2 * v_pre ) + 1 ) < 400020) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells2 ) ” 
  &&  “ (TreeOK cells2 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
) \/
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre )) (PreH3 : (CellsAgreeOutside ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre cells cells1 )) (PreH4 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (lo_pre <> hi_pre)) (PreH6 : (NodeFits v_pre lo_pre hi_pre )) (PreH7 : (hi_pre <= n)) (PreH8 : (n = (Zlength (arr)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 100000)) (PreH11 : (lo_pre <= pos_pre)) (PreH12 : (pos_pre <= hi_pre)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  TT && emp 
|--
  “ (CellsAgreeOutside v_pre lo_pre hi_pre cells cells1 ) ” 
  &&  “ (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ (((2 * v_pre ) + 1 ) < 400020) ” 
  &&  “ (lo_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (1 <= lo_pre) ”
  &&  emp
).

Definition update_entail_wit_3_2_split_goal_1 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre )) (PreH3 : (CellsAgreeOutside ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre cells cells1 )) (PreH4 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (lo_pre <> hi_pre)) (PreH6 : (NodeFits v_pre lo_pre hi_pre )) (PreH7 : (hi_pre <= n)) (PreH8 : (n = (Zlength (arr)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 100000)) (PreH11 : (lo_pre <= pos_pre)) (PreH12 : (pos_pre <= hi_pre)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (CellsAgreeOutside v_pre lo_pre hi_pre cells cells1 )
.

Definition update_entail_wit_3_2_split_goal_2 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre )) (PreH3 : (CellsAgreeOutside ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre cells cells1 )) (PreH4 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (lo_pre <> hi_pre)) (PreH6 : (NodeFits v_pre lo_pre hi_pre )) (PreH7 : (hi_pre <= n)) (PreH8 : (n = (Zlength (arr)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 100000)) (PreH11 : (lo_pre <= pos_pre)) (PreH12 : (pos_pre <= hi_pre)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (TreeOK cells1 arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) )
.

Definition update_entail_wit_3_2_split_goal_3 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre )) (PreH3 : (CellsAgreeOutside ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre cells cells1 )) (PreH4 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (lo_pre <> hi_pre)) (PreH6 : (NodeFits v_pre lo_pre hi_pre )) (PreH7 : (hi_pre <= n)) (PreH8 : (n = (Zlength (arr)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 100000)) (PreH11 : (lo_pre <= pos_pre)) (PreH12 : (pos_pre <= hi_pre)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (((2 * v_pre ) + 1 ) < 400020)
.

Definition update_entail_wit_3_2_split_goal_4 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre )) (PreH3 : (CellsAgreeOutside ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre cells cells1 )) (PreH4 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (lo_pre <> hi_pre)) (PreH6 : (NodeFits v_pre lo_pre hi_pre )) (PreH7 : (hi_pre <= n)) (PreH8 : (n = (Zlength (arr)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 100000)) (PreH11 : (lo_pre <= pos_pre)) (PreH12 : (pos_pre <= hi_pre)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (lo_pre <= ((lo_pre + hi_pre ) ÷ 2 ))
.

Definition update_entail_wit_3_2_split_goal_5 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre )) (PreH3 : (CellsAgreeOutside ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre cells cells1 )) (PreH4 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (lo_pre <> hi_pre)) (PreH6 : (NodeFits v_pre lo_pre hi_pre )) (PreH7 : (hi_pre <= n)) (PreH8 : (n = (Zlength (arr)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 100000)) (PreH11 : (lo_pre <= pos_pre)) (PreH12 : (pos_pre <= hi_pre)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (1 <= lo_pre)
.

Definition update_return_wit_1 := 
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (r >= 60)) (PreH2 : (lo_pre = hi_pre)) (PreH3 : (lo_pre = pos_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  EX (cells1: (@list (@list (@option Z)))) ,
  “ (CellsShaped cells1 ) ” 
  &&  “ (TreeOK cells1 arr v_pre lo_pre hi_pre ) ” 
  &&  “ (CellsAgreeOutside v_pre lo_pre hi_pre cells cells1 ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
) \/
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (r >= 60)) (PreH2 : (lo_pre = hi_pre)) (PreH3 : (lo_pre = pos_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  TT && emp 
|--
  “ (CellsAgreeOutside v_pre hi_pre hi_pre cells cellsr ) ” 
  &&  “ (TreeOK cellsr arr v_pre hi_pre hi_pre ) ”
  &&  emp
).

Definition update_return_wit_1_split_goal_1 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (r >= 60)) (PreH2 : (lo_pre = hi_pre)) (PreH3 : (lo_pre = pos_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (CellsAgreeOutside v_pre hi_pre hi_pre cells cellsr )
.

Definition update_return_wit_1_split_goal_2 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (r >= 60)) (PreH2 : (lo_pre = hi_pre)) (PreH3 : (lo_pre = pos_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (TreeOK cellsr arr v_pre hi_pre hi_pre )
.

Definition update_return_wit_2 := 
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (cells1_2: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1_2 )) (PreH2 : (RowIs cells1_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) )) (PreH3 : (RowsAgreeExcept v_pre cells2 cells1_2 )) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= lo_pre)) (PreH6 : (lo_pre <= mid)) (PreH7 : (mid < hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH13 : (lo_pre <= pos_pre)) (PreH14 : (pos_pre <= hi_pre)) (PreH15 : (((2 * v_pre ) + 1 ) < 400020)) (PreH16 : (PeriodsOK arr )) (PreH17 : (CellsShaped cells2 )) (PreH18 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH19 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH20 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1_2 )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
|--
  EX (cells1: (@list (@list (@option Z)))) ,
  “ (CellsShaped cells1 ) ” 
  &&  “ (TreeOK cells1 arr v_pre lo_pre hi_pre ) ” 
  &&  “ (CellsAgreeOutside v_pre lo_pre hi_pre cells cells1 ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
) \/
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (cells1_2: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1_2 )) (PreH2 : (RowIs cells1_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) )) (PreH3 : (RowsAgreeExcept v_pre cells2 cells1_2 )) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= lo_pre)) (PreH6 : (lo_pre <= mid)) (PreH7 : (mid < hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH13 : (lo_pre <= pos_pre)) (PreH14 : (pos_pre <= hi_pre)) (PreH15 : (((2 * v_pre ) + 1 ) < 400020)) (PreH16 : (PeriodsOK arr )) (PreH17 : (CellsShaped cells2 )) (PreH18 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH19 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH20 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  TT && emp 
|--
  “ (CellsAgreeOutside v_pre lo_pre hi_pre cells cells1_2 ) ” 
  &&  “ (TreeOK cells1_2 arr v_pre lo_pre hi_pre ) ”
  &&  emp
).

Definition update_return_wit_2_split_goal_1 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (cells1_2: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1_2 )) (PreH2 : (RowIs cells1_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) )) (PreH3 : (RowsAgreeExcept v_pre cells2 cells1_2 )) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= lo_pre)) (PreH6 : (lo_pre <= mid)) (PreH7 : (mid < hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH13 : (lo_pre <= pos_pre)) (PreH14 : (pos_pre <= hi_pre)) (PreH15 : (((2 * v_pre ) + 1 ) < 400020)) (PreH16 : (PeriodsOK arr )) (PreH17 : (CellsShaped cells2 )) (PreH18 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH19 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH20 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  (CellsAgreeOutside v_pre lo_pre hi_pre cells cells1_2 )
.

Definition update_return_wit_2_split_goal_2 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (cells1_2: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1_2 )) (PreH2 : (RowIs cells1_2 v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) )) (PreH3 : (RowsAgreeExcept v_pre cells2 cells1_2 )) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= lo_pre)) (PreH6 : (lo_pre <= mid)) (PreH7 : (mid < hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH13 : (lo_pre <= pos_pre)) (PreH14 : (pos_pre <= hi_pre)) (PreH15 : (((2 * v_pre ) + 1 ) < 400020)) (PreH16 : (PeriodsOK arr )) (PreH17 : (CellsShaped cells2 )) (PreH18 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH19 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH20 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  (TreeOK cells1_2 arr v_pre lo_pre hi_pre )
.

Definition update_partial_solve_wit_1 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z) (PreH1 : (r < 60)) (PreH2 : (lo_pre = hi_pre)) (PreH3 : (lo_pre = pos_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= n)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH14 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH15 : (0 <= r)) (PreH16 : (r <= 60)) (PreH17 : (PeriodsOK arr )) (PreH18 : (CellsShaped cellsr )) (PreH19 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH20 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ (r < 60) ” 
  &&  “ (lo_pre = hi_pre) ” 
  &&  “ (lo_pre = pos_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= n) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (2 <= (Znth ((lo_pre - 1 )) (arr) (0))) ” 
  &&  “ ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r <= 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cellsr ) ” 
  &&  “ (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r ) ” 
  &&  “ (RowsAgreeExcept v_pre cells cellsr ) ”
  &&  (((( &( "a_" ) ) + (lo_pre * sizeof(INT)))) # Int  |-> (Znth (lo_pre - 1 ) arr 0))
  **  (IntArray.missing_i ( &( "a_" ) ) lo_pre 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
.

Definition update_partial_solve_wit_2 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) = 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (lo_pre = pos_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= n)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH15 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH16 : (0 <= r)) (PreH17 : (r <= 60)) (PreH18 : (PeriodsOK arr )) (PreH19 : (CellsShaped cellsr )) (PreH20 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH21 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) = 0) ” 
  &&  “ (r < 60) ” 
  &&  “ (lo_pre = hi_pre) ” 
  &&  “ (lo_pre = pos_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= n) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (2 <= (Znth ((lo_pre - 1 )) (arr) (0))) ” 
  &&  “ ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r <= 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cellsr ) ” 
  &&  “ (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r ) ” 
  &&  “ (RowsAgreeExcept v_pre cells cellsr ) ”
  &&  ((((( &( "seg" ) ) + (v_pre * (sizeof(INT) * 60))) + (r * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i (( &( "seg" ) ) + (v_pre * (sizeof(INT) * 60))) r 0 60 (Znth v_pre cellsr __default__List__App_option_Z) )
  **  (IntArray2.mixed_missing_i ( &( "seg" ) ) v_pre 0 400020 60 cellsr )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
.

Definition update_partial_solve_wit_3 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cellsr: (@list (@list (@option Z)))) (r: Z)  __default__List__App_option_Z (PreH1 : ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) <> 0)) (PreH2 : (r < 60)) (PreH3 : (lo_pre = hi_pre)) (PreH4 : (lo_pre = pos_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= n)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (2 <= (Znth ((lo_pre - 1 )) (arr) (0)))) (PreH15 : ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6)) (PreH16 : (0 <= r)) (PreH17 : (r <= 60)) (PreH18 : (PeriodsOK arr )) (PreH19 : (CellsShaped cellsr )) (PreH20 : (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r )) (PreH21 : (RowsAgreeExcept v_pre cells cellsr )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cellsr )
|--
  “ ((r % ( (Znth (lo_pre - 1 ) arr 0) ) ) <> 0) ” 
  &&  “ (r < 60) ” 
  &&  “ (lo_pre = hi_pre) ” 
  &&  “ (lo_pre = pos_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= n) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (2 <= (Znth ((lo_pre - 1 )) (arr) (0))) ” 
  &&  “ ((Znth ((lo_pre - 1 )) (arr) (0)) <= 6) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r <= 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cellsr ) ” 
  &&  “ (RowPrefixIs cellsr v_pre (NodeSlice (arr) (lo_pre) (hi_pre)) r ) ” 
  &&  “ (RowsAgreeExcept v_pre cells cellsr ) ”
  &&  ((((( &( "seg" ) ) + (v_pre * (sizeof(INT) * 60))) + (r * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i (( &( "seg" ) ) + (v_pre * (sizeof(INT) * 60))) r 0 60 (Znth v_pre cellsr __default__List__App_option_Z) )
  **  (IntArray2.mixed_missing_i ( &( "seg" ) ) v_pre 0 400020 60 cellsr )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
.

Definition update_partial_solve_wit_4_pure := 
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (lo_pre <= pos_pre) ” 
  &&  “ (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeStaleAt cells arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) pos_pre ) ” 
  &&  “ (((lo_pre + hi_pre ) ÷ 2 ) <= n) ” 
  &&  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ”
) \/
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre <= INT_MAX)) (PreH2 : (hi_pre <= INT_MAX)) (PreH3 : (lo_pre <= INT_MAX)) (PreH4 : (v_pre <= INT_MAX)) (PreH5 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH6 : (pos_pre >= INT_MIN)) (PreH7 : (hi_pre >= INT_MIN)) (PreH8 : (lo_pre >= INT_MIN)) (PreH9 : (v_pre >= INT_MIN)) (PreH10 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH11 : (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH12 : (lo_pre <> hi_pre)) (PreH13 : (NodeFits v_pre lo_pre hi_pre )) (PreH14 : (hi_pre <= n)) (PreH15 : (n = (Zlength (arr)))) (PreH16 : (1 <= n)) (PreH17 : (n <= 100000)) (PreH18 : (lo_pre <= pos_pre)) (PreH19 : (pos_pre <= hi_pre)) (PreH20 : (PeriodsOK arr )) (PreH21 : (CellsShaped cells )) (PreH22 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ (((lo_pre + hi_pre ) ÷ 2 ) <= n) ” 
  &&  “ (TreeStaleAt cells arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) pos_pre ) ”
).

Definition update_partial_solve_wit_4_pure_split_goal_1 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre <= INT_MAX)) (PreH2 : (hi_pre <= INT_MAX)) (PreH3 : (lo_pre <= INT_MAX)) (PreH4 : (v_pre <= INT_MAX)) (PreH5 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH6 : (pos_pre >= INT_MIN)) (PreH7 : (hi_pre >= INT_MIN)) (PreH8 : (lo_pre >= INT_MIN)) (PreH9 : (v_pre >= INT_MIN)) (PreH10 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH11 : (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH12 : (lo_pre <> hi_pre)) (PreH13 : (NodeFits v_pre lo_pre hi_pre )) (PreH14 : (hi_pre <= n)) (PreH15 : (n = (Zlength (arr)))) (PreH16 : (1 <= n)) (PreH17 : (n <= 100000)) (PreH18 : (lo_pre <= pos_pre)) (PreH19 : (pos_pre <= hi_pre)) (PreH20 : (PeriodsOK arr )) (PreH21 : (CellsShaped cells )) (PreH22 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ”
.

Definition update_partial_solve_wit_4_pure_split_goal_2 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre <= INT_MAX)) (PreH2 : (hi_pre <= INT_MAX)) (PreH3 : (lo_pre <= INT_MAX)) (PreH4 : (v_pre <= INT_MAX)) (PreH5 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH6 : (pos_pre >= INT_MIN)) (PreH7 : (hi_pre >= INT_MIN)) (PreH8 : (lo_pre >= INT_MIN)) (PreH9 : (v_pre >= INT_MIN)) (PreH10 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH11 : (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH12 : (lo_pre <> hi_pre)) (PreH13 : (NodeFits v_pre lo_pre hi_pre )) (PreH14 : (hi_pre <= n)) (PreH15 : (n = (Zlength (arr)))) (PreH16 : (1 <= n)) (PreH17 : (n <= 100000)) (PreH18 : (lo_pre <= pos_pre)) (PreH19 : (pos_pre <= hi_pre)) (PreH20 : (PeriodsOK arr )) (PreH21 : (CellsShaped cells )) (PreH22 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (((lo_pre + hi_pre ) ÷ 2 ) <= n) ”
.

Definition update_partial_solve_wit_4_pure_split_goal_3 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre <= INT_MAX)) (PreH2 : (hi_pre <= INT_MAX)) (PreH3 : (lo_pre <= INT_MAX)) (PreH4 : (v_pre <= INT_MAX)) (PreH5 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH6 : (pos_pre >= INT_MIN)) (PreH7 : (hi_pre >= INT_MIN)) (PreH8 : (lo_pre >= INT_MIN)) (PreH9 : (v_pre >= INT_MIN)) (PreH10 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH11 : (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH12 : (lo_pre <> hi_pre)) (PreH13 : (NodeFits v_pre lo_pre hi_pre )) (PreH14 : (hi_pre <= n)) (PreH15 : (n = (Zlength (arr)))) (PreH16 : (1 <= n)) (PreH17 : (n <= 100000)) (PreH18 : (lo_pre <= pos_pre)) (PreH19 : (pos_pre <= hi_pre)) (PreH20 : (PeriodsOK arr )) (PreH21 : (CellsShaped cells )) (PreH22 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (TreeStaleAt cells arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) pos_pre ) ”
.

Definition update_partial_solve_wit_4_aux := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (lo_pre <= pos_pre) ” 
  &&  “ (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeStaleAt cells arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) pos_pre ) ” 
  &&  “ (((lo_pre + hi_pre ) ÷ 2 ) <= n) ” 
  &&  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ (pos_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (lo_pre <> hi_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (lo_pre <= pos_pre) ” 
  &&  “ (pos_pre <= hi_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
.

Definition update_partial_solve_wit_4 := update_partial_solve_wit_4_pure -> update_partial_solve_wit_4_aux.

Definition update_partial_solve_wit_5_pure := 
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((((lo_pre + hi_pre ) ÷ 2 ) + 1 ) <= pos_pre) ” 
  &&  “ (pos_pre <= hi_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeStaleAt cells arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre pos_pre ) ” 
  &&  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
) \/
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre <= INT_MAX)) (PreH2 : (hi_pre <= INT_MAX)) (PreH3 : (lo_pre <= INT_MAX)) (PreH4 : (v_pre <= INT_MAX)) (PreH5 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH6 : (pos_pre >= INT_MIN)) (PreH7 : (hi_pre >= INT_MIN)) (PreH8 : (lo_pre >= INT_MIN)) (PreH9 : (v_pre >= INT_MIN)) (PreH10 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH11 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH12 : (lo_pre <> hi_pre)) (PreH13 : (NodeFits v_pre lo_pre hi_pre )) (PreH14 : (hi_pre <= n)) (PreH15 : (n = (Zlength (arr)))) (PreH16 : (1 <= n)) (PreH17 : (n <= 100000)) (PreH18 : (lo_pre <= pos_pre)) (PreH19 : (pos_pre <= hi_pre)) (PreH20 : (PeriodsOK arr )) (PreH21 : (CellsShaped cells )) (PreH22 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ (TreeStaleAt cells arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre pos_pre ) ”
).

Definition update_partial_solve_wit_5_pure_split_goal_1 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre <= INT_MAX)) (PreH2 : (hi_pre <= INT_MAX)) (PreH3 : (lo_pre <= INT_MAX)) (PreH4 : (v_pre <= INT_MAX)) (PreH5 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH6 : (pos_pre >= INT_MIN)) (PreH7 : (hi_pre >= INT_MIN)) (PreH8 : (lo_pre >= INT_MIN)) (PreH9 : (v_pre >= INT_MIN)) (PreH10 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH11 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH12 : (lo_pre <> hi_pre)) (PreH13 : (NodeFits v_pre lo_pre hi_pre )) (PreH14 : (hi_pre <= n)) (PreH15 : (n = (Zlength (arr)))) (PreH16 : (1 <= n)) (PreH17 : (n <= 100000)) (PreH18 : (lo_pre <= pos_pre)) (PreH19 : (pos_pre <= hi_pre)) (PreH20 : (PeriodsOK arr )) (PreH21 : (CellsShaped cells )) (PreH22 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
.

Definition update_partial_solve_wit_5_pure_split_goal_2 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre <= INT_MAX)) (PreH2 : (hi_pre <= INT_MAX)) (PreH3 : (lo_pre <= INT_MAX)) (PreH4 : (v_pre <= INT_MAX)) (PreH5 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH6 : (pos_pre >= INT_MIN)) (PreH7 : (hi_pre >= INT_MIN)) (PreH8 : (lo_pre >= INT_MIN)) (PreH9 : (v_pre >= INT_MIN)) (PreH10 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH11 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH12 : (lo_pre <> hi_pre)) (PreH13 : (NodeFits v_pre lo_pre hi_pre )) (PreH14 : (hi_pre <= n)) (PreH15 : (n = (Zlength (arr)))) (PreH16 : (1 <= n)) (PreH17 : (n <= 100000)) (PreH18 : (lo_pre <= pos_pre)) (PreH19 : (pos_pre <= hi_pre)) (PreH20 : (PeriodsOK arr )) (PreH21 : (CellsShaped cells )) (PreH22 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (TreeStaleAt cells arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre pos_pre ) ”
.

Definition update_partial_solve_wit_5_aux := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (pos_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (lo_pre <> hi_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (hi_pre <= n)) (PreH5 : (n = (Zlength (arr)))) (PreH6 : (1 <= n)) (PreH7 : (n <= 100000)) (PreH8 : (lo_pre <= pos_pre)) (PreH9 : (pos_pre <= hi_pre)) (PreH10 : (PeriodsOK arr )) (PreH11 : (CellsShaped cells )) (PreH12 : (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ ((((lo_pre + hi_pre ) ÷ 2 ) + 1 ) <= pos_pre) ” 
  &&  “ (pos_pre <= hi_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeStaleAt cells arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre pos_pre ) ” 
  &&  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ (pos_pre > ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (lo_pre <> hi_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (lo_pre <= pos_pre) ” 
  &&  “ (pos_pre <= hi_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeStaleAt cells arr v_pre lo_pre hi_pre pos_pre ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
.

Definition update_partial_solve_wit_5 := update_partial_solve_wit_5_pure -> update_partial_solve_wit_5_aux.

Definition update_partial_solve_wit_6_pure := 
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (PreH1 : (NodeFits v_pre lo_pre hi_pre )) (PreH2 : (1 <= lo_pre)) (PreH3 : (lo_pre <= mid)) (PreH4 : (mid < hi_pre)) (PreH5 : (hi_pre <= n)) (PreH6 : (n = (Zlength (arr)))) (PreH7 : (1 <= n)) (PreH8 : (n <= 100000)) (PreH9 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH10 : (lo_pre <= pos_pre)) (PreH11 : (pos_pre <= hi_pre)) (PreH12 : (((2 * v_pre ) + 1 ) < 400020)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells2 )) (PreH15 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH16 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH17 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
|--
  “ (((2 * v_pre ) + 1 ) < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= mid) ” 
  &&  “ (mid < hi_pre) ” 
  &&  “ (hi_pre <= (Zlength (arr))) ” 
  &&  “ ((Zlength (arr)) <= 100000) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells2 ) ” 
  &&  “ (RowIs cells2 (2 * v_pre ) (NodeSlice (arr) (lo_pre) (mid)) ) ” 
  &&  “ (RowIs cells2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi_pre)) ) ” 
  &&  “ (RowIs cells2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre)) ) ” 
  &&  “ (RowIs cells2 (2 * v_pre ) (NodeSlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 ))) ) ” 
  &&  “ (1 <= v_pre) ”
) \/
(
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (PreH1 : (mid <= INT_MAX)) (PreH2 : (pos_pre <= INT_MAX)) (PreH3 : (hi_pre <= INT_MAX)) (PreH4 : (lo_pre <= INT_MAX)) (PreH5 : (v_pre <= INT_MAX)) (PreH6 : (mid >= INT_MIN)) (PreH7 : (pos_pre >= INT_MIN)) (PreH8 : (hi_pre >= INT_MIN)) (PreH9 : (lo_pre >= INT_MIN)) (PreH10 : (v_pre >= INT_MIN)) (PreH11 : (NodeFits v_pre lo_pre hi_pre )) (PreH12 : (1 <= lo_pre)) (PreH13 : (lo_pre <= mid)) (PreH14 : (mid < hi_pre)) (PreH15 : (hi_pre <= n)) (PreH16 : (n = (Zlength (arr)))) (PreH17 : (1 <= n)) (PreH18 : (n <= 100000)) (PreH19 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH20 : (lo_pre <= pos_pre)) (PreH21 : (pos_pre <= hi_pre)) (PreH22 : (((2 * v_pre ) + 1 ) < 400020)) (PreH23 : (PeriodsOK arr )) (PreH24 : (CellsShaped cells2 )) (PreH25 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH26 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH27 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
|--
  “ (1 <= v_pre) ” 
  &&  “ (RowIs cells2 (2 * v_pre ) (NodeSlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 ))) ) ” 
  &&  “ (RowIs cells2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre)) ) ” 
  &&  “ (RowIs cells2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre)) ) ” 
  &&  “ (RowIs cells2 (2 * v_pre ) (NodeSlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 ))) ) ”
).

Definition update_partial_solve_wit_6_pure_split_goal_1 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (PreH1 : (mid <= INT_MAX)) (PreH2 : (pos_pre <= INT_MAX)) (PreH3 : (hi_pre <= INT_MAX)) (PreH4 : (lo_pre <= INT_MAX)) (PreH5 : (v_pre <= INT_MAX)) (PreH6 : (mid >= INT_MIN)) (PreH7 : (pos_pre >= INT_MIN)) (PreH8 : (hi_pre >= INT_MIN)) (PreH9 : (lo_pre >= INT_MIN)) (PreH10 : (v_pre >= INT_MIN)) (PreH11 : (NodeFits v_pre lo_pre hi_pre )) (PreH12 : (1 <= lo_pre)) (PreH13 : (lo_pre <= mid)) (PreH14 : (mid < hi_pre)) (PreH15 : (hi_pre <= n)) (PreH16 : (n = (Zlength (arr)))) (PreH17 : (1 <= n)) (PreH18 : (n <= 100000)) (PreH19 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH20 : (lo_pre <= pos_pre)) (PreH21 : (pos_pre <= hi_pre)) (PreH22 : (((2 * v_pre ) + 1 ) < 400020)) (PreH23 : (PeriodsOK arr )) (PreH24 : (CellsShaped cells2 )) (PreH25 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH26 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH27 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
|--
  “ (1 <= v_pre) ”
.

Definition update_partial_solve_wit_6_pure_split_goal_2 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (PreH1 : (mid <= INT_MAX)) (PreH2 : (pos_pre <= INT_MAX)) (PreH3 : (hi_pre <= INT_MAX)) (PreH4 : (lo_pre <= INT_MAX)) (PreH5 : (v_pre <= INT_MAX)) (PreH6 : (mid >= INT_MIN)) (PreH7 : (pos_pre >= INT_MIN)) (PreH8 : (hi_pre >= INT_MIN)) (PreH9 : (lo_pre >= INT_MIN)) (PreH10 : (v_pre >= INT_MIN)) (PreH11 : (NodeFits v_pre lo_pre hi_pre )) (PreH12 : (1 <= lo_pre)) (PreH13 : (lo_pre <= mid)) (PreH14 : (mid < hi_pre)) (PreH15 : (hi_pre <= n)) (PreH16 : (n = (Zlength (arr)))) (PreH17 : (1 <= n)) (PreH18 : (n <= 100000)) (PreH19 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH20 : (lo_pre <= pos_pre)) (PreH21 : (pos_pre <= hi_pre)) (PreH22 : (((2 * v_pre ) + 1 ) < 400020)) (PreH23 : (PeriodsOK arr )) (PreH24 : (CellsShaped cells2 )) (PreH25 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH26 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH27 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
|--
  “ (RowIs cells2 (2 * v_pre ) (NodeSlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 ))) ) ”
.

Definition update_partial_solve_wit_6_pure_split_goal_3 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (PreH1 : (mid <= INT_MAX)) (PreH2 : (pos_pre <= INT_MAX)) (PreH3 : (hi_pre <= INT_MAX)) (PreH4 : (lo_pre <= INT_MAX)) (PreH5 : (v_pre <= INT_MAX)) (PreH6 : (mid >= INT_MIN)) (PreH7 : (pos_pre >= INT_MIN)) (PreH8 : (hi_pre >= INT_MIN)) (PreH9 : (lo_pre >= INT_MIN)) (PreH10 : (v_pre >= INT_MIN)) (PreH11 : (NodeFits v_pre lo_pre hi_pre )) (PreH12 : (1 <= lo_pre)) (PreH13 : (lo_pre <= mid)) (PreH14 : (mid < hi_pre)) (PreH15 : (hi_pre <= n)) (PreH16 : (n = (Zlength (arr)))) (PreH17 : (1 <= n)) (PreH18 : (n <= 100000)) (PreH19 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH20 : (lo_pre <= pos_pre)) (PreH21 : (pos_pre <= hi_pre)) (PreH22 : (((2 * v_pre ) + 1 ) < 400020)) (PreH23 : (PeriodsOK arr )) (PreH24 : (CellsShaped cells2 )) (PreH25 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH26 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH27 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
|--
  “ (RowIs cells2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre)) ) ”
.

Definition update_partial_solve_wit_6_pure_split_goal_4 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (PreH1 : (mid <= INT_MAX)) (PreH2 : (pos_pre <= INT_MAX)) (PreH3 : (hi_pre <= INT_MAX)) (PreH4 : (lo_pre <= INT_MAX)) (PreH5 : (v_pre <= INT_MAX)) (PreH6 : (mid >= INT_MIN)) (PreH7 : (pos_pre >= INT_MIN)) (PreH8 : (hi_pre >= INT_MIN)) (PreH9 : (lo_pre >= INT_MIN)) (PreH10 : (v_pre >= INT_MIN)) (PreH11 : (NodeFits v_pre lo_pre hi_pre )) (PreH12 : (1 <= lo_pre)) (PreH13 : (lo_pre <= mid)) (PreH14 : (mid < hi_pre)) (PreH15 : (hi_pre <= n)) (PreH16 : (n = (Zlength (arr)))) (PreH17 : (1 <= n)) (PreH18 : (n <= 100000)) (PreH19 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH20 : (lo_pre <= pos_pre)) (PreH21 : (pos_pre <= hi_pre)) (PreH22 : (((2 * v_pre ) + 1 ) < 400020)) (PreH23 : (PeriodsOK arr )) (PreH24 : (CellsShaped cells2 )) (PreH25 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH26 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH27 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
|--
  “ (RowIs cells2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre)) ) ”
.

Definition update_partial_solve_wit_6_pure_split_goal_5 := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (PreH1 : (mid <= INT_MAX)) (PreH2 : (pos_pre <= INT_MAX)) (PreH3 : (hi_pre <= INT_MAX)) (PreH4 : (lo_pre <= INT_MAX)) (PreH5 : (v_pre <= INT_MAX)) (PreH6 : (mid >= INT_MIN)) (PreH7 : (pos_pre >= INT_MIN)) (PreH8 : (hi_pre >= INT_MIN)) (PreH9 : (lo_pre >= INT_MIN)) (PreH10 : (v_pre >= INT_MIN)) (PreH11 : (NodeFits v_pre lo_pre hi_pre )) (PreH12 : (1 <= lo_pre)) (PreH13 : (lo_pre <= mid)) (PreH14 : (mid < hi_pre)) (PreH15 : (hi_pre <= n)) (PreH16 : (n = (Zlength (arr)))) (PreH17 : (1 <= n)) (PreH18 : (n <= 100000)) (PreH19 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH20 : (lo_pre <= pos_pre)) (PreH21 : (pos_pre <= hi_pre)) (PreH22 : (((2 * v_pre ) + 1 ) < 400020)) (PreH23 : (PeriodsOK arr )) (PreH24 : (CellsShaped cells2 )) (PreH25 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH26 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH27 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
|--
  “ (RowIs cells2 (2 * v_pre ) (NodeSlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 ))) ) ”
.

Definition update_partial_solve_wit_6_aux := 
forall (pos_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (cells2: (@list (@list (@option Z)))) (mid: Z) (PreH1 : (NodeFits v_pre lo_pre hi_pre )) (PreH2 : (1 <= lo_pre)) (PreH3 : (lo_pre <= mid)) (PreH4 : (mid < hi_pre)) (PreH5 : (hi_pre <= n)) (PreH6 : (n = (Zlength (arr)))) (PreH7 : (1 <= n)) (PreH8 : (n <= 100000)) (PreH9 : (mid = ((lo_pre + hi_pre ) ÷ 2 ))) (PreH10 : (lo_pre <= pos_pre)) (PreH11 : (pos_pre <= hi_pre)) (PreH12 : (((2 * v_pre ) + 1 ) < 400020)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells2 )) (PreH15 : (TreeOK cells2 arr (2 * v_pre ) lo_pre mid )) (PreH16 : (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre )) (PreH17 : (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
|--
  “ (((2 * v_pre ) + 1 ) < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= mid) ” 
  &&  “ (mid < hi_pre) ” 
  &&  “ (hi_pre <= (Zlength (arr))) ” 
  &&  “ ((Zlength (arr)) <= 100000) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells2 ) ” 
  &&  “ (RowIs cells2 (2 * v_pre ) (NodeSlice (arr) (lo_pre) (mid)) ) ” 
  &&  “ (RowIs cells2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((mid + 1 )) (hi_pre)) ) ” 
  &&  “ (RowIs cells2 ((2 * v_pre ) + 1 ) (NodeSlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre)) ) ” 
  &&  “ (RowIs cells2 (2 * v_pre ) (NodeSlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 ))) ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= mid) ” 
  &&  “ (mid < hi_pre) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (mid = ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (lo_pre <= pos_pre) ” 
  &&  “ (pos_pre <= hi_pre) ” 
  &&  “ (((2 * v_pre ) + 1 ) < 400020) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells2 ) ” 
  &&  “ (TreeOK cells2 arr (2 * v_pre ) lo_pre mid ) ” 
  &&  “ (TreeOK cells2 arr ((2 * v_pre ) + 1 ) (mid + 1 ) hi_pre ) ” 
  &&  “ (CellsAgreeOutside v_pre lo_pre hi_pre cells cells2 ) ”
  &&  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells2 )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
.

Definition update_partial_solve_wit_6 := update_partial_solve_wit_6_pure -> update_partial_solve_wit_6_aux.

(*----- Function query -----*)

Definition query_safety_wit_1 := 
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z))))  __default__List__App_option_Z (PreH1 : (hi_pre <= qr_pre)) (PreH2 : (ql_pre <= lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (v_pre) ((replace_Znth ((t_pre % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) )))))) ((Znth v_pre cells __default__List__App_option_Z)))) (cells)) )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
|--
  “ ((t_pre + (Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) ))) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (t_pre + (Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) ))) )) ”
) \/
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z))))  __default__List__App_option_Z (PreH1 : (hi_pre <= qr_pre)) (PreH2 : (ql_pre <= lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (v_pre) ((replace_Znth ((t_pre % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) )))))) ((Znth v_pre cells __default__List__App_option_Z)))) (cells)) )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
|--
  “ ((t_pre + (Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) ))) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (t_pre + (Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) ))) )) ”
).

Definition query_safety_wit_1_split_goal_1 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z))))  __default__List__App_option_Z (PreH1 : (hi_pre <= qr_pre)) (PreH2 : (ql_pre <= lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (v_pre) ((replace_Znth ((t_pre % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) )))))) ((Znth v_pre cells __default__List__App_option_Z)))) (cells)) )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
|--
  “ ((t_pre + (Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) ))) ) <= INT_MAX) ”
.

Definition query_safety_wit_1_split_goal_2 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z))))  __default__List__App_option_Z (PreH1 : (hi_pre <= qr_pre)) (PreH2 : (ql_pre <= lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (v_pre) ((replace_Znth ((t_pre % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) )))))) ((Znth v_pre cells __default__List__App_option_Z)))) (cells)) )
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
|--
  “ ((INT_MIN) <= (t_pre + (Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) ))) )) ”
.

Definition query_safety_wit_2 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (hi_pre <= qr_pre)) (PreH2 : (ql_pre <= lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((t_pre <> (INT_MIN)) \/ (60 <> (-1))) ” 
  &&  “ (60 <> 0) ”
.

Definition query_safety_wit_3 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (hi_pre <= qr_pre)) (PreH2 : (ql_pre <= lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (60 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 60) ”
.

Definition query_safety_wit_4 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre > lo_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (1 <= v_pre)) (PreH4 : (v_pre < 400020)) (PreH5 : (1 <= lo_pre)) (PreH6 : (lo_pre <= hi_pre)) (PreH7 : (hi_pre <= n)) (PreH8 : (n = (Zlength (arr)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 100000)) (PreH11 : (1 <= ql_pre)) (PreH12 : (ql_pre <= qr_pre)) (PreH13 : (qr_pre <= n)) (PreH14 : (lo_pre <= qr_pre)) (PreH15 : (ql_pre <= hi_pre)) (PreH16 : (0 <= t_pre)) (PreH17 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH18 : (0 <= (t_pre % ( 60 ) ))) (PreH19 : ((t_pre % ( 60 ) ) < 60)) (PreH20 : (PeriodsOK arr )) (PreH21 : (CellsShaped cells )) (PreH22 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (((lo_pre + hi_pre ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition query_safety_wit_5 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre > lo_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (1 <= v_pre)) (PreH4 : (v_pre < 400020)) (PreH5 : (1 <= lo_pre)) (PreH6 : (lo_pre <= hi_pre)) (PreH7 : (hi_pre <= n)) (PreH8 : (n = (Zlength (arr)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 100000)) (PreH11 : (1 <= ql_pre)) (PreH12 : (ql_pre <= qr_pre)) (PreH13 : (qr_pre <= n)) (PreH14 : (lo_pre <= qr_pre)) (PreH15 : (ql_pre <= hi_pre)) (PreH16 : (0 <= t_pre)) (PreH17 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH18 : (0 <= (t_pre % ( 60 ) ))) (PreH19 : ((t_pre % ( 60 ) ) < 60)) (PreH20 : (PeriodsOK arr )) (PreH21 : (CellsShaped cells )) (PreH22 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((lo_pre + hi_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lo_pre + hi_pre )) ”
.

Definition query_safety_wit_6 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre > lo_pre)) (PreH2 : (NodeFits v_pre lo_pre hi_pre )) (PreH3 : (1 <= v_pre)) (PreH4 : (v_pre < 400020)) (PreH5 : (1 <= lo_pre)) (PreH6 : (lo_pre <= hi_pre)) (PreH7 : (hi_pre <= n)) (PreH8 : (n = (Zlength (arr)))) (PreH9 : (1 <= n)) (PreH10 : (n <= 100000)) (PreH11 : (1 <= ql_pre)) (PreH12 : (ql_pre <= qr_pre)) (PreH13 : (qr_pre <= n)) (PreH14 : (lo_pre <= qr_pre)) (PreH15 : (ql_pre <= hi_pre)) (PreH16 : (0 <= t_pre)) (PreH17 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH18 : (0 <= (t_pre % ( 60 ) ))) (PreH19 : ((t_pre % ( 60 ) ) < 60)) (PreH20 : (PeriodsOK arr )) (PreH21 : (CellsShaped cells )) (PreH22 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition query_safety_wit_7 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (hi_pre > qr_pre)) (PreH2 : (ql_pre <= lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (((lo_pre + hi_pre ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition query_safety_wit_8 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (hi_pre > qr_pre)) (PreH2 : (ql_pre <= lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((lo_pre + hi_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lo_pre + hi_pre )) ”
.

Definition query_safety_wit_9 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (hi_pre > qr_pre)) (PreH2 : (ql_pre <= lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition query_safety_wit_10 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (ql_pre > lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((2 * v_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * v_pre )) ”
.

Definition query_safety_wit_11 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (ql_pre > lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition query_safety_wit_12 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (hi_pre > qr_pre)) (PreH3 : (ql_pre <= lo_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= hi_pre)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (1 <= ql_pre)) (PreH14 : (ql_pre <= qr_pre)) (PreH15 : (qr_pre <= n)) (PreH16 : (lo_pre <= qr_pre)) (PreH17 : (ql_pre <= hi_pre)) (PreH18 : (0 <= t_pre)) (PreH19 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH20 : (0 <= (t_pre % ( 60 ) ))) (PreH21 : ((t_pre % ( 60 ) ) < 60)) (PreH22 : (PeriodsOK arr )) (PreH23 : (CellsShaped cells )) (PreH24 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((2 * v_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * v_pre )) ”
.

Definition query_safety_wit_13 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (hi_pre > qr_pre)) (PreH3 : (ql_pre <= lo_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= hi_pre)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (1 <= ql_pre)) (PreH14 : (ql_pre <= qr_pre)) (PreH15 : (qr_pre <= n)) (PreH16 : (lo_pre <= qr_pre)) (PreH17 : (ql_pre <= hi_pre)) (PreH18 : (0 <= t_pre)) (PreH19 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH20 : (0 <= (t_pre % ( 60 ) ))) (PreH21 : ((t_pre % ( 60 ) ) < 60)) (PreH22 : (PeriodsOK arr )) (PreH23 : (CellsShaped cells )) (PreH24 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition query_safety_wit_14 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (ql_pre > lo_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= hi_pre)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (1 <= ql_pre)) (PreH14 : (ql_pre <= qr_pre)) (PreH15 : (qr_pre <= n)) (PreH16 : (lo_pre <= qr_pre)) (PreH17 : (ql_pre <= hi_pre)) (PreH18 : (0 <= t_pre)) (PreH19 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH20 : (0 <= (t_pre % ( 60 ) ))) (PreH21 : ((t_pre % ( 60 ) ) < 60)) (PreH22 : (PeriodsOK arr )) (PreH23 : (CellsShaped cells )) (PreH24 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((((lo_pre + hi_pre ) ÷ 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((lo_pre + hi_pre ) ÷ 2 ) + 1 )) ”
.

Definition query_safety_wit_15 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (ql_pre > lo_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= hi_pre)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (1 <= ql_pre)) (PreH14 : (ql_pre <= qr_pre)) (PreH15 : (qr_pre <= n)) (PreH16 : (lo_pre <= qr_pre)) (PreH17 : (ql_pre <= hi_pre)) (PreH18 : (0 <= t_pre)) (PreH19 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH20 : (0 <= (t_pre % ( 60 ) ))) (PreH21 : ((t_pre % ( 60 ) ) < 60)) (PreH22 : (PeriodsOK arr )) (PreH23 : (CellsShaped cells )) (PreH24 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (((2 * v_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * v_pre ) + 1 )) ”
.

Definition query_safety_wit_16 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (ql_pre > lo_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= hi_pre)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (1 <= ql_pre)) (PreH14 : (ql_pre <= qr_pre)) (PreH15 : (qr_pre <= n)) (PreH16 : (lo_pre <= qr_pre)) (PreH17 : (ql_pre <= hi_pre)) (PreH18 : (0 <= t_pre)) (PreH19 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH20 : (0 <= (t_pre % ( 60 ) ))) (PreH21 : ((t_pre % ( 60 ) ) < 60)) (PreH22 : (PeriodsOK arr )) (PreH23 : (CellsShaped cells )) (PreH24 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((2 * v_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * v_pre )) ”
.

Definition query_safety_wit_17 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (ql_pre > lo_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= hi_pre)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (1 <= ql_pre)) (PreH14 : (ql_pre <= qr_pre)) (PreH15 : (qr_pre <= n)) (PreH16 : (lo_pre <= qr_pre)) (PreH17 : (ql_pre <= hi_pre)) (PreH18 : (0 <= t_pre)) (PreH19 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH20 : (0 <= (t_pre % ( 60 ) ))) (PreH21 : ((t_pre % ( 60 ) ) < 60)) (PreH22 : (PeriodsOK arr )) (PreH23 : (CellsShaped cells )) (PreH24 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition query_safety_wit_18 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (ql_pre > lo_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= hi_pre)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (1 <= ql_pre)) (PreH14 : (ql_pre <= qr_pre)) (PreH15 : (qr_pre <= n)) (PreH16 : (lo_pre <= qr_pre)) (PreH17 : (ql_pre <= hi_pre)) (PreH18 : (0 <= t_pre)) (PreH19 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH20 : (0 <= (t_pre % ( 60 ) ))) (PreH21 : ((t_pre % ( 60 ) ) < 60)) (PreH22 : (PeriodsOK arr )) (PreH23 : (CellsShaped cells )) (PreH24 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition query_safety_wit_19 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (ql_pre > lo_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= hi_pre)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (1 <= ql_pre)) (PreH14 : (ql_pre <= qr_pre)) (PreH15 : (qr_pre <= n)) (PreH16 : (lo_pre <= qr_pre)) (PreH17 : (ql_pre <= hi_pre)) (PreH18 : (0 <= t_pre)) (PreH19 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH20 : (0 <= (t_pre % ( 60 ) ))) (PreH21 : ((t_pre % ( 60 ) ) < 60)) (PreH22 : (PeriodsOK arr )) (PreH23 : (CellsShaped cells )) (PreH24 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition query_safety_wit_20 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (hi_pre > qr_pre)) (PreH4 : (ql_pre <= lo_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= hi_pre)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (1 <= ql_pre)) (PreH15 : (ql_pre <= qr_pre)) (PreH16 : (qr_pre <= n)) (PreH17 : (lo_pre <= qr_pre)) (PreH18 : (ql_pre <= hi_pre)) (PreH19 : (0 <= t_pre)) (PreH20 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH21 : (0 <= (t_pre % ( 60 ) ))) (PreH22 : ((t_pre % ( 60 ) ) < 60)) (PreH23 : (PeriodsOK arr )) (PreH24 : (CellsShaped cells )) (PreH25 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((((lo_pre + hi_pre ) ÷ 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((lo_pre + hi_pre ) ÷ 2 ) + 1 )) ”
.

Definition query_safety_wit_21 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (hi_pre > qr_pre)) (PreH4 : (ql_pre <= lo_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= hi_pre)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (1 <= ql_pre)) (PreH15 : (ql_pre <= qr_pre)) (PreH16 : (qr_pre <= n)) (PreH17 : (lo_pre <= qr_pre)) (PreH18 : (ql_pre <= hi_pre)) (PreH19 : (0 <= t_pre)) (PreH20 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH21 : (0 <= (t_pre % ( 60 ) ))) (PreH22 : ((t_pre % ( 60 ) ) < 60)) (PreH23 : (PeriodsOK arr )) (PreH24 : (CellsShaped cells )) (PreH25 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (((2 * v_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * v_pre ) + 1 )) ”
.

Definition query_safety_wit_22 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (hi_pre > qr_pre)) (PreH4 : (ql_pre <= lo_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= hi_pre)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (1 <= ql_pre)) (PreH15 : (ql_pre <= qr_pre)) (PreH16 : (qr_pre <= n)) (PreH17 : (lo_pre <= qr_pre)) (PreH18 : (ql_pre <= hi_pre)) (PreH19 : (0 <= t_pre)) (PreH20 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH21 : (0 <= (t_pre % ( 60 ) ))) (PreH22 : ((t_pre % ( 60 ) ) < 60)) (PreH23 : (PeriodsOK arr )) (PreH24 : (CellsShaped cells )) (PreH25 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((2 * v_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * v_pre )) ”
.

Definition query_safety_wit_23 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (hi_pre > qr_pre)) (PreH4 : (ql_pre <= lo_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= hi_pre)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (1 <= ql_pre)) (PreH15 : (ql_pre <= qr_pre)) (PreH16 : (qr_pre <= n)) (PreH17 : (lo_pre <= qr_pre)) (PreH18 : (ql_pre <= hi_pre)) (PreH19 : (0 <= t_pre)) (PreH20 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH21 : (0 <= (t_pre % ( 60 ) ))) (PreH22 : ((t_pre % ( 60 ) ) < 60)) (PreH23 : (PeriodsOK arr )) (PreH24 : (CellsShaped cells )) (PreH25 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition query_safety_wit_24 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (hi_pre > qr_pre)) (PreH4 : (ql_pre <= lo_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= hi_pre)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (1 <= ql_pre)) (PreH15 : (ql_pre <= qr_pre)) (PreH16 : (qr_pre <= n)) (PreH17 : (lo_pre <= qr_pre)) (PreH18 : (ql_pre <= hi_pre)) (PreH19 : (0 <= t_pre)) (PreH20 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH21 : (0 <= (t_pre % ( 60 ) ))) (PreH22 : ((t_pre % ( 60 ) ) < 60)) (PreH23 : (PeriodsOK arr )) (PreH24 : (CellsShaped cells )) (PreH25 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition query_safety_wit_25 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (hi_pre > qr_pre)) (PreH4 : (ql_pre <= lo_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= hi_pre)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (1 <= ql_pre)) (PreH15 : (ql_pre <= qr_pre)) (PreH16 : (qr_pre <= n)) (PreH17 : (lo_pre <= qr_pre)) (PreH18 : (ql_pre <= hi_pre)) (PreH19 : (0 <= t_pre)) (PreH20 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH21 : (0 <= (t_pre % ( 60 ) ))) (PreH22 : ((t_pre % ( 60 ) ) < 60)) (PreH23 : (PeriodsOK arr )) (PreH24 : (CellsShaped cells )) (PreH25 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition query_safety_wit_26 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (ql_pre > lo_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= hi_pre)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (1 <= ql_pre)) (PreH14 : (ql_pre <= qr_pre)) (PreH15 : (qr_pre <= n)) (PreH16 : (lo_pre <= qr_pre)) (PreH17 : (ql_pre <= hi_pre)) (PreH18 : (0 <= t_pre)) (PreH19 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH20 : (0 <= (t_pre % ( 60 ) ))) (PreH21 : ((t_pre % ( 60 ) ) < 60)) (PreH22 : (PeriodsOK arr )) (PreH23 : (CellsShaped cells )) (PreH24 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mt" ) )) # Int  |->_)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((2 * v_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * v_pre )) ”
.

Definition query_safety_wit_27 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (ql_pre > lo_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= hi_pre)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (1 <= ql_pre)) (PreH14 : (ql_pre <= qr_pre)) (PreH15 : (qr_pre <= n)) (PreH16 : (lo_pre <= qr_pre)) (PreH17 : (ql_pre <= hi_pre)) (PreH18 : (0 <= t_pre)) (PreH19 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH20 : (0 <= (t_pre % ( 60 ) ))) (PreH21 : ((t_pre % ( 60 ) ) < 60)) (PreH22 : (PeriodsOK arr )) (PreH23 : (CellsShaped cells )) (PreH24 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mt" ) )) # Int  |->_)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition query_safety_wit_28 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (hi_pre > qr_pre)) (PreH4 : (ql_pre <= lo_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= hi_pre)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (1 <= ql_pre)) (PreH15 : (ql_pre <= qr_pre)) (PreH16 : (qr_pre <= n)) (PreH17 : (lo_pre <= qr_pre)) (PreH18 : (ql_pre <= hi_pre)) (PreH19 : (0 <= t_pre)) (PreH20 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH21 : (0 <= (t_pre % ( 60 ) ))) (PreH22 : ((t_pre % ( 60 ) ) < 60)) (PreH23 : (PeriodsOK arr )) (PreH24 : (CellsShaped cells )) (PreH25 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mt" ) )) # Int  |->_)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((2 * v_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * v_pre )) ”
.

Definition query_safety_wit_29 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (hi_pre > qr_pre)) (PreH4 : (ql_pre <= lo_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= hi_pre)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (1 <= ql_pre)) (PreH15 : (ql_pre <= qr_pre)) (PreH16 : (qr_pre <= n)) (PreH17 : (lo_pre <= qr_pre)) (PreH18 : (ql_pre <= hi_pre)) (PreH19 : (0 <= t_pre)) (PreH20 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH21 : (0 <= (t_pre % ( 60 ) ))) (PreH22 : ((t_pre % ( 60 ) ) < 60)) (PreH23 : (PeriodsOK arr )) (PreH24 : (CellsShaped cells )) (PreH25 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mt" ) )) # Int  |->_)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition query_safety_wit_30 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (ql_pre > lo_pre)) (PreH7 : (NodeFits v_pre lo_pre hi_pre )) (PreH8 : (1 <= v_pre)) (PreH9 : (v_pre < 400020)) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= hi_pre)) (PreH12 : (hi_pre <= n)) (PreH13 : (n = (Zlength (arr)))) (PreH14 : (1 <= n)) (PreH15 : (n <= 100000)) (PreH16 : (1 <= ql_pre)) (PreH17 : (ql_pre <= qr_pre)) (PreH18 : (qr_pre <= n)) (PreH19 : (lo_pre <= qr_pre)) (PreH20 : (ql_pre <= hi_pre)) (PreH21 : (0 <= t_pre)) (PreH22 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH23 : (0 <= (t_pre % ( 60 ) ))) (PreH24 : ((t_pre % ( 60 ) ) < 60)) (PreH25 : (PeriodsOK arr )) (PreH26 : (CellsShaped cells )) (PreH27 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  ((( &( "mt" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  “ ((((lo_pre + hi_pre ) ÷ 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((lo_pre + hi_pre ) ÷ 2 ) + 1 )) ”
.

Definition query_safety_wit_31 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (ql_pre > lo_pre)) (PreH7 : (NodeFits v_pre lo_pre hi_pre )) (PreH8 : (1 <= v_pre)) (PreH9 : (v_pre < 400020)) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= hi_pre)) (PreH12 : (hi_pre <= n)) (PreH13 : (n = (Zlength (arr)))) (PreH14 : (1 <= n)) (PreH15 : (n <= 100000)) (PreH16 : (1 <= ql_pre)) (PreH17 : (ql_pre <= qr_pre)) (PreH18 : (qr_pre <= n)) (PreH19 : (lo_pre <= qr_pre)) (PreH20 : (ql_pre <= hi_pre)) (PreH21 : (0 <= t_pre)) (PreH22 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH23 : (0 <= (t_pre % ( 60 ) ))) (PreH24 : ((t_pre % ( 60 ) ) < 60)) (PreH25 : (PeriodsOK arr )) (PreH26 : (CellsShaped cells )) (PreH27 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  ((( &( "mt" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  “ (((2 * v_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * v_pre ) + 1 )) ”
.

Definition query_safety_wit_32 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (ql_pre > lo_pre)) (PreH7 : (NodeFits v_pre lo_pre hi_pre )) (PreH8 : (1 <= v_pre)) (PreH9 : (v_pre < 400020)) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= hi_pre)) (PreH12 : (hi_pre <= n)) (PreH13 : (n = (Zlength (arr)))) (PreH14 : (1 <= n)) (PreH15 : (n <= 100000)) (PreH16 : (1 <= ql_pre)) (PreH17 : (ql_pre <= qr_pre)) (PreH18 : (qr_pre <= n)) (PreH19 : (lo_pre <= qr_pre)) (PreH20 : (ql_pre <= hi_pre)) (PreH21 : (0 <= t_pre)) (PreH22 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH23 : (0 <= (t_pre % ( 60 ) ))) (PreH24 : ((t_pre % ( 60 ) ) < 60)) (PreH25 : (PeriodsOK arr )) (PreH26 : (CellsShaped cells )) (PreH27 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  ((( &( "mt" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  “ ((2 * v_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * v_pre )) ”
.

Definition query_safety_wit_33 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (ql_pre > lo_pre)) (PreH7 : (NodeFits v_pre lo_pre hi_pre )) (PreH8 : (1 <= v_pre)) (PreH9 : (v_pre < 400020)) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= hi_pre)) (PreH12 : (hi_pre <= n)) (PreH13 : (n = (Zlength (arr)))) (PreH14 : (1 <= n)) (PreH15 : (n <= 100000)) (PreH16 : (1 <= ql_pre)) (PreH17 : (ql_pre <= qr_pre)) (PreH18 : (qr_pre <= n)) (PreH19 : (lo_pre <= qr_pre)) (PreH20 : (ql_pre <= hi_pre)) (PreH21 : (0 <= t_pre)) (PreH22 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH23 : (0 <= (t_pre % ( 60 ) ))) (PreH24 : ((t_pre % ( 60 ) ) < 60)) (PreH25 : (PeriodsOK arr )) (PreH26 : (CellsShaped cells )) (PreH27 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  ((( &( "mt" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition query_safety_wit_34 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (ql_pre > lo_pre)) (PreH7 : (NodeFits v_pre lo_pre hi_pre )) (PreH8 : (1 <= v_pre)) (PreH9 : (v_pre < 400020)) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= hi_pre)) (PreH12 : (hi_pre <= n)) (PreH13 : (n = (Zlength (arr)))) (PreH14 : (1 <= n)) (PreH15 : (n <= 100000)) (PreH16 : (1 <= ql_pre)) (PreH17 : (ql_pre <= qr_pre)) (PreH18 : (qr_pre <= n)) (PreH19 : (lo_pre <= qr_pre)) (PreH20 : (ql_pre <= hi_pre)) (PreH21 : (0 <= t_pre)) (PreH22 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH23 : (0 <= (t_pre % ( 60 ) ))) (PreH24 : ((t_pre % ( 60 ) ) < 60)) (PreH25 : (PeriodsOK arr )) (PreH26 : (CellsShaped cells )) (PreH27 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  ((( &( "mt" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition query_safety_wit_35 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (ql_pre > lo_pre)) (PreH7 : (NodeFits v_pre lo_pre hi_pre )) (PreH8 : (1 <= v_pre)) (PreH9 : (v_pre < 400020)) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= hi_pre)) (PreH12 : (hi_pre <= n)) (PreH13 : (n = (Zlength (arr)))) (PreH14 : (1 <= n)) (PreH15 : (n <= 100000)) (PreH16 : (1 <= ql_pre)) (PreH17 : (ql_pre <= qr_pre)) (PreH18 : (qr_pre <= n)) (PreH19 : (lo_pre <= qr_pre)) (PreH20 : (ql_pre <= hi_pre)) (PreH21 : (0 <= t_pre)) (PreH22 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH23 : (0 <= (t_pre % ( 60 ) ))) (PreH24 : ((t_pre % ( 60 ) ) < 60)) (PreH25 : (PeriodsOK arr )) (PreH26 : (CellsShaped cells )) (PreH27 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  ((( &( "mt" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition query_safety_wit_36 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (hi_pre > qr_pre)) (PreH7 : (ql_pre <= lo_pre)) (PreH8 : (NodeFits v_pre lo_pre hi_pre )) (PreH9 : (1 <= v_pre)) (PreH10 : (v_pre < 400020)) (PreH11 : (1 <= lo_pre)) (PreH12 : (lo_pre <= hi_pre)) (PreH13 : (hi_pre <= n)) (PreH14 : (n = (Zlength (arr)))) (PreH15 : (1 <= n)) (PreH16 : (n <= 100000)) (PreH17 : (1 <= ql_pre)) (PreH18 : (ql_pre <= qr_pre)) (PreH19 : (qr_pre <= n)) (PreH20 : (lo_pre <= qr_pre)) (PreH21 : (ql_pre <= hi_pre)) (PreH22 : (0 <= t_pre)) (PreH23 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH24 : (0 <= (t_pre % ( 60 ) ))) (PreH25 : ((t_pre % ( 60 ) ) < 60)) (PreH26 : (PeriodsOK arr )) (PreH27 : (CellsShaped cells )) (PreH28 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  ((( &( "mt" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  “ ((((lo_pre + hi_pre ) ÷ 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((lo_pre + hi_pre ) ÷ 2 ) + 1 )) ”
.

Definition query_safety_wit_37 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (hi_pre > qr_pre)) (PreH7 : (ql_pre <= lo_pre)) (PreH8 : (NodeFits v_pre lo_pre hi_pre )) (PreH9 : (1 <= v_pre)) (PreH10 : (v_pre < 400020)) (PreH11 : (1 <= lo_pre)) (PreH12 : (lo_pre <= hi_pre)) (PreH13 : (hi_pre <= n)) (PreH14 : (n = (Zlength (arr)))) (PreH15 : (1 <= n)) (PreH16 : (n <= 100000)) (PreH17 : (1 <= ql_pre)) (PreH18 : (ql_pre <= qr_pre)) (PreH19 : (qr_pre <= n)) (PreH20 : (lo_pre <= qr_pre)) (PreH21 : (ql_pre <= hi_pre)) (PreH22 : (0 <= t_pre)) (PreH23 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH24 : (0 <= (t_pre % ( 60 ) ))) (PreH25 : ((t_pre % ( 60 ) ) < 60)) (PreH26 : (PeriodsOK arr )) (PreH27 : (CellsShaped cells )) (PreH28 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  ((( &( "mt" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  “ (((2 * v_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * v_pre ) + 1 )) ”
.

Definition query_safety_wit_38 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (hi_pre > qr_pre)) (PreH7 : (ql_pre <= lo_pre)) (PreH8 : (NodeFits v_pre lo_pre hi_pre )) (PreH9 : (1 <= v_pre)) (PreH10 : (v_pre < 400020)) (PreH11 : (1 <= lo_pre)) (PreH12 : (lo_pre <= hi_pre)) (PreH13 : (hi_pre <= n)) (PreH14 : (n = (Zlength (arr)))) (PreH15 : (1 <= n)) (PreH16 : (n <= 100000)) (PreH17 : (1 <= ql_pre)) (PreH18 : (ql_pre <= qr_pre)) (PreH19 : (qr_pre <= n)) (PreH20 : (lo_pre <= qr_pre)) (PreH21 : (ql_pre <= hi_pre)) (PreH22 : (0 <= t_pre)) (PreH23 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH24 : (0 <= (t_pre % ( 60 ) ))) (PreH25 : ((t_pre % ( 60 ) ) < 60)) (PreH26 : (PeriodsOK arr )) (PreH27 : (CellsShaped cells )) (PreH28 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  ((( &( "mt" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  “ ((2 * v_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * v_pre )) ”
.

Definition query_safety_wit_39 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (hi_pre > qr_pre)) (PreH7 : (ql_pre <= lo_pre)) (PreH8 : (NodeFits v_pre lo_pre hi_pre )) (PreH9 : (1 <= v_pre)) (PreH10 : (v_pre < 400020)) (PreH11 : (1 <= lo_pre)) (PreH12 : (lo_pre <= hi_pre)) (PreH13 : (hi_pre <= n)) (PreH14 : (n = (Zlength (arr)))) (PreH15 : (1 <= n)) (PreH16 : (n <= 100000)) (PreH17 : (1 <= ql_pre)) (PreH18 : (ql_pre <= qr_pre)) (PreH19 : (qr_pre <= n)) (PreH20 : (lo_pre <= qr_pre)) (PreH21 : (ql_pre <= hi_pre)) (PreH22 : (0 <= t_pre)) (PreH23 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH24 : (0 <= (t_pre % ( 60 ) ))) (PreH25 : ((t_pre % ( 60 ) ) < 60)) (PreH26 : (PeriodsOK arr )) (PreH27 : (CellsShaped cells )) (PreH28 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  ((( &( "mt" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition query_safety_wit_40 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (hi_pre > qr_pre)) (PreH7 : (ql_pre <= lo_pre)) (PreH8 : (NodeFits v_pre lo_pre hi_pre )) (PreH9 : (1 <= v_pre)) (PreH10 : (v_pre < 400020)) (PreH11 : (1 <= lo_pre)) (PreH12 : (lo_pre <= hi_pre)) (PreH13 : (hi_pre <= n)) (PreH14 : (n = (Zlength (arr)))) (PreH15 : (1 <= n)) (PreH16 : (n <= 100000)) (PreH17 : (1 <= ql_pre)) (PreH18 : (ql_pre <= qr_pre)) (PreH19 : (qr_pre <= n)) (PreH20 : (lo_pre <= qr_pre)) (PreH21 : (ql_pre <= hi_pre)) (PreH22 : (0 <= t_pre)) (PreH23 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH24 : (0 <= (t_pre % ( 60 ) ))) (PreH25 : ((t_pre % ( 60 ) ) < 60)) (PreH26 : (PeriodsOK arr )) (PreH27 : (CellsShaped cells )) (PreH28 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  ((( &( "mt" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition query_safety_wit_41 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (hi_pre > qr_pre)) (PreH7 : (ql_pre <= lo_pre)) (PreH8 : (NodeFits v_pre lo_pre hi_pre )) (PreH9 : (1 <= v_pre)) (PreH10 : (v_pre < 400020)) (PreH11 : (1 <= lo_pre)) (PreH12 : (lo_pre <= hi_pre)) (PreH13 : (hi_pre <= n)) (PreH14 : (n = (Zlength (arr)))) (PreH15 : (1 <= n)) (PreH16 : (n <= 100000)) (PreH17 : (1 <= ql_pre)) (PreH18 : (ql_pre <= qr_pre)) (PreH19 : (qr_pre <= n)) (PreH20 : (lo_pre <= qr_pre)) (PreH21 : (ql_pre <= hi_pre)) (PreH22 : (0 <= t_pre)) (PreH23 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH24 : (0 <= (t_pre % ( 60 ) ))) (PreH25 : ((t_pre % ( 60 ) ) < 60)) (PreH26 : (PeriodsOK arr )) (PreH27 : (CellsShaped cells )) (PreH28 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  ((( &( "mt" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition query_entail_wit_1 := 
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (NodeFits v_pre lo_pre hi_pre )) (PreH2 : (hi_pre <= n)) (PreH3 : (n = (Zlength (arr)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 100000)) (PreH6 : (1 <= ql_pre)) (PreH7 : (ql_pre <= qr_pre)) (PreH8 : (qr_pre <= n)) (PreH9 : (lo_pre <= qr_pre)) (PreH10 : (ql_pre <= hi_pre)) (PreH11 : (0 <= t_pre)) (PreH12 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ (lo_pre <= qr_pre) ” 
  &&  “ (ql_pre <= hi_pre) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (0 <= (t_pre % ( 60 ) )) ” 
  &&  “ ((t_pre % ( 60 ) ) < 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr v_pre lo_pre hi_pre ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
) \/
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (NodeFits v_pre lo_pre hi_pre )) (PreH2 : (hi_pre <= n)) (PreH3 : (n = (Zlength (arr)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 100000)) (PreH6 : (1 <= ql_pre)) (PreH7 : (ql_pre <= qr_pre)) (PreH8 : (qr_pre <= n)) (PreH9 : (lo_pre <= qr_pre)) (PreH10 : (ql_pre <= hi_pre)) (PreH11 : (0 <= t_pre)) (PreH12 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  TT && emp 
|--
  “ ((t_pre % ( 60 ) ) < 60) ” 
  &&  “ (0 <= (t_pre % ( 60 ) )) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= v_pre) ”
  &&  emp
).

Definition query_entail_wit_1_split_goal_1 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (NodeFits v_pre lo_pre hi_pre )) (PreH2 : (hi_pre <= n)) (PreH3 : (n = (Zlength (arr)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 100000)) (PreH6 : (1 <= ql_pre)) (PreH7 : (ql_pre <= qr_pre)) (PreH8 : (qr_pre <= n)) (PreH9 : (lo_pre <= qr_pre)) (PreH10 : (ql_pre <= hi_pre)) (PreH11 : (0 <= t_pre)) (PreH12 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((t_pre % ( 60 ) ) < 60)
.

Definition query_entail_wit_1_split_goal_2 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (NodeFits v_pre lo_pre hi_pre )) (PreH2 : (hi_pre <= n)) (PreH3 : (n = (Zlength (arr)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 100000)) (PreH6 : (1 <= ql_pre)) (PreH7 : (ql_pre <= qr_pre)) (PreH8 : (qr_pre <= n)) (PreH9 : (lo_pre <= qr_pre)) (PreH10 : (ql_pre <= hi_pre)) (PreH11 : (0 <= t_pre)) (PreH12 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (0 <= (t_pre % ( 60 ) ))
.

Definition query_entail_wit_1_split_goal_3 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (NodeFits v_pre lo_pre hi_pre )) (PreH2 : (hi_pre <= n)) (PreH3 : (n = (Zlength (arr)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 100000)) (PreH6 : (1 <= ql_pre)) (PreH7 : (ql_pre <= qr_pre)) (PreH8 : (qr_pre <= n)) (PreH9 : (lo_pre <= qr_pre)) (PreH10 : (ql_pre <= hi_pre)) (PreH11 : (0 <= t_pre)) (PreH12 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (lo_pre <= hi_pre)
.

Definition query_entail_wit_1_split_goal_4 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (NodeFits v_pre lo_pre hi_pre )) (PreH2 : (hi_pre <= n)) (PreH3 : (n = (Zlength (arr)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 100000)) (PreH6 : (1 <= ql_pre)) (PreH7 : (ql_pre <= qr_pre)) (PreH8 : (qr_pre <= n)) (PreH9 : (lo_pre <= qr_pre)) (PreH10 : (ql_pre <= hi_pre)) (PreH11 : (0 <= t_pre)) (PreH12 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (1 <= lo_pre)
.

Definition query_entail_wit_1_split_goal_5 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (NodeFits v_pre lo_pre hi_pre )) (PreH2 : (hi_pre <= n)) (PreH3 : (n = (Zlength (arr)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 100000)) (PreH6 : (1 <= ql_pre)) (PreH7 : (ql_pre <= qr_pre)) (PreH8 : (qr_pre <= n)) (PreH9 : (lo_pre <= qr_pre)) (PreH10 : (ql_pre <= hi_pre)) (PreH11 : (0 <= t_pre)) (PreH12 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (v_pre < 400020)
.

Definition query_entail_wit_1_split_goal_6 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (NodeFits v_pre lo_pre hi_pre )) (PreH2 : (hi_pre <= n)) (PreH3 : (n = (Zlength (arr)))) (PreH4 : (1 <= n)) (PreH5 : (n <= 100000)) (PreH6 : (1 <= ql_pre)) (PreH7 : (ql_pre <= qr_pre)) (PreH8 : (qr_pre <= n)) (PreH9 : (lo_pre <= qr_pre)) (PreH10 : (ql_pre <= hi_pre)) (PreH11 : (0 <= t_pre)) (PreH12 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH13 : (PeriodsOK arr )) (PreH14 : (CellsShaped cells )) (PreH15 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (1 <= v_pre)
.

Definition query_return_wit_1 := 
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval_2: Z) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2)))) (PreH2 : (retval_2 <= retval)) (PreH3 : (retval <= (retval_2 + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ))) (PreH4 : (retval_2 = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH5 : (t_pre <= retval_2)) (PreH6 : (retval_2 <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH7 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH8 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH9 : (ql_pre > lo_pre)) (PreH10 : (NodeFits v_pre lo_pre hi_pre )) (PreH11 : (1 <= v_pre)) (PreH12 : (v_pre < 400020)) (PreH13 : (1 <= lo_pre)) (PreH14 : (lo_pre <= hi_pre)) (PreH15 : (hi_pre <= n)) (PreH16 : (n = (Zlength (arr)))) (PreH17 : (1 <= n)) (PreH18 : (n <= 100000)) (PreH19 : (1 <= ql_pre)) (PreH20 : (ql_pre <= qr_pre)) (PreH21 : (qr_pre <= n)) (PreH22 : (lo_pre <= qr_pre)) (PreH23 : (ql_pre <= hi_pre)) (PreH24 : (0 <= t_pre)) (PreH25 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH26 : (0 <= (t_pre % ( 60 ) ))) (PreH27 : ((t_pre % ( 60 ) ) < 60)) (PreH28 : (PeriodsOK arr )) (PreH29 : (CellsShaped cells )) (PreH30 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (retval = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre))) ” 
  &&  “ (t_pre <= retval) ” 
  &&  “ (retval <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) )) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
) \/
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval_2: Z) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2)))) (PreH2 : (retval_2 <= retval)) (PreH3 : (retval <= (retval_2 + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ))) (PreH4 : (retval_2 = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH5 : (t_pre <= retval_2)) (PreH6 : (retval_2 <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH7 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH8 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH9 : (ql_pre > lo_pre)) (PreH10 : (NodeFits v_pre lo_pre hi_pre )) (PreH11 : (1 <= v_pre)) (PreH12 : (v_pre < 400020)) (PreH13 : (1 <= lo_pre)) (PreH14 : (lo_pre <= hi_pre)) (PreH15 : (hi_pre <= n)) (PreH16 : (n = (Zlength (arr)))) (PreH17 : (1 <= n)) (PreH18 : (n <= 100000)) (PreH19 : (1 <= ql_pre)) (PreH20 : (ql_pre <= qr_pre)) (PreH21 : (qr_pre <= n)) (PreH22 : (lo_pre <= qr_pre)) (PreH23 : (ql_pre <= hi_pre)) (PreH24 : (0 <= t_pre)) (PreH25 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH26 : (0 <= (t_pre % ( 60 ) ))) (PreH27 : ((t_pre % ( 60 ) ) < 60)) (PreH28 : (PeriodsOK arr )) (PreH29 : (CellsShaped cells )) (PreH30 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  TT && emp 
|--
  “ ((cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2)) <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) )) ” 
  &&  “ (t_pre <= (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2))) ” 
  &&  “ ((cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2)) = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre))) ”
  &&  emp
).

Definition query_return_wit_1_split_goal_1 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval_2: Z) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2)))) (PreH2 : (retval_2 <= retval)) (PreH3 : (retval <= (retval_2 + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ))) (PreH4 : (retval_2 = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH5 : (t_pre <= retval_2)) (PreH6 : (retval_2 <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH7 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH8 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH9 : (ql_pre > lo_pre)) (PreH10 : (NodeFits v_pre lo_pre hi_pre )) (PreH11 : (1 <= v_pre)) (PreH12 : (v_pre < 400020)) (PreH13 : (1 <= lo_pre)) (PreH14 : (lo_pre <= hi_pre)) (PreH15 : (hi_pre <= n)) (PreH16 : (n = (Zlength (arr)))) (PreH17 : (1 <= n)) (PreH18 : (n <= 100000)) (PreH19 : (1 <= ql_pre)) (PreH20 : (ql_pre <= qr_pre)) (PreH21 : (qr_pre <= n)) (PreH22 : (lo_pre <= qr_pre)) (PreH23 : (ql_pre <= hi_pre)) (PreH24 : (0 <= t_pre)) (PreH25 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH26 : (0 <= (t_pre % ( 60 ) ))) (PreH27 : ((t_pre % ( 60 ) ) < 60)) (PreH28 : (PeriodsOK arr )) (PreH29 : (CellsShaped cells )) (PreH30 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2)) <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ))
.

Definition query_return_wit_1_split_goal_2 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval_2: Z) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2)))) (PreH2 : (retval_2 <= retval)) (PreH3 : (retval <= (retval_2 + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ))) (PreH4 : (retval_2 = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH5 : (t_pre <= retval_2)) (PreH6 : (retval_2 <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH7 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH8 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH9 : (ql_pre > lo_pre)) (PreH10 : (NodeFits v_pre lo_pre hi_pre )) (PreH11 : (1 <= v_pre)) (PreH12 : (v_pre < 400020)) (PreH13 : (1 <= lo_pre)) (PreH14 : (lo_pre <= hi_pre)) (PreH15 : (hi_pre <= n)) (PreH16 : (n = (Zlength (arr)))) (PreH17 : (1 <= n)) (PreH18 : (n <= 100000)) (PreH19 : (1 <= ql_pre)) (PreH20 : (ql_pre <= qr_pre)) (PreH21 : (qr_pre <= n)) (PreH22 : (lo_pre <= qr_pre)) (PreH23 : (ql_pre <= hi_pre)) (PreH24 : (0 <= t_pre)) (PreH25 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH26 : (0 <= (t_pre % ( 60 ) ))) (PreH27 : ((t_pre % ( 60 ) ) < 60)) (PreH28 : (PeriodsOK arr )) (PreH29 : (CellsShaped cells )) (PreH30 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (t_pre <= (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2)))
.

Definition query_return_wit_1_split_goal_3 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval_2: Z) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2)))) (PreH2 : (retval_2 <= retval)) (PreH3 : (retval <= (retval_2 + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ))) (PreH4 : (retval_2 = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH5 : (t_pre <= retval_2)) (PreH6 : (retval_2 <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH7 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH8 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH9 : (ql_pre > lo_pre)) (PreH10 : (NodeFits v_pre lo_pre hi_pre )) (PreH11 : (1 <= v_pre)) (PreH12 : (v_pre < 400020)) (PreH13 : (1 <= lo_pre)) (PreH14 : (lo_pre <= hi_pre)) (PreH15 : (hi_pre <= n)) (PreH16 : (n = (Zlength (arr)))) (PreH17 : (1 <= n)) (PreH18 : (n <= 100000)) (PreH19 : (1 <= ql_pre)) (PreH20 : (ql_pre <= qr_pre)) (PreH21 : (qr_pre <= n)) (PreH22 : (lo_pre <= qr_pre)) (PreH23 : (ql_pre <= hi_pre)) (PreH24 : (0 <= t_pre)) (PreH25 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH26 : (0 <= (t_pre % ( 60 ) ))) (PreH27 : ((t_pre % ( 60 ) ) < 60)) (PreH28 : (PeriodsOK arr )) (PreH29 : (CellsShaped cells )) (PreH30 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2)) = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre)))
.

Definition query_return_wit_2 := 
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval_2: Z) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2)))) (PreH2 : (retval_2 <= retval)) (PreH3 : (retval <= (retval_2 + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ))) (PreH4 : (retval_2 = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH5 : (t_pre <= retval_2)) (PreH6 : (retval_2 <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH7 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH8 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH9 : (hi_pre > qr_pre)) (PreH10 : (ql_pre <= lo_pre)) (PreH11 : (NodeFits v_pre lo_pre hi_pre )) (PreH12 : (1 <= v_pre)) (PreH13 : (v_pre < 400020)) (PreH14 : (1 <= lo_pre)) (PreH15 : (lo_pre <= hi_pre)) (PreH16 : (hi_pre <= n)) (PreH17 : (n = (Zlength (arr)))) (PreH18 : (1 <= n)) (PreH19 : (n <= 100000)) (PreH20 : (1 <= ql_pre)) (PreH21 : (ql_pre <= qr_pre)) (PreH22 : (qr_pre <= n)) (PreH23 : (lo_pre <= qr_pre)) (PreH24 : (ql_pre <= hi_pre)) (PreH25 : (0 <= t_pre)) (PreH26 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH27 : (0 <= (t_pre % ( 60 ) ))) (PreH28 : ((t_pre % ( 60 ) ) < 60)) (PreH29 : (PeriodsOK arr )) (PreH30 : (CellsShaped cells )) (PreH31 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (retval = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre))) ” 
  &&  “ (t_pre <= retval) ” 
  &&  “ (retval <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) )) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
) \/
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval_2: Z) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2)))) (PreH2 : (retval_2 <= retval)) (PreH3 : (retval <= (retval_2 + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ))) (PreH4 : (retval_2 = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH5 : (t_pre <= retval_2)) (PreH6 : (retval_2 <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH7 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH8 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH9 : (hi_pre > qr_pre)) (PreH10 : (ql_pre <= lo_pre)) (PreH11 : (NodeFits v_pre lo_pre hi_pre )) (PreH12 : (1 <= v_pre)) (PreH13 : (v_pre < 400020)) (PreH14 : (1 <= lo_pre)) (PreH15 : (lo_pre <= hi_pre)) (PreH16 : (hi_pre <= n)) (PreH17 : (n = (Zlength (arr)))) (PreH18 : (1 <= n)) (PreH19 : (n <= 100000)) (PreH20 : (1 <= ql_pre)) (PreH21 : (ql_pre <= qr_pre)) (PreH22 : (qr_pre <= n)) (PreH23 : (lo_pre <= qr_pre)) (PreH24 : (ql_pre <= hi_pre)) (PreH25 : (0 <= t_pre)) (PreH26 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH27 : (0 <= (t_pre % ( 60 ) ))) (PreH28 : ((t_pre % ( 60 ) ) < 60)) (PreH29 : (PeriodsOK arr )) (PreH30 : (CellsShaped cells )) (PreH31 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  TT && emp 
|--
  “ ((cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2)) <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) )) ” 
  &&  “ (t_pre <= (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2))) ” 
  &&  “ ((cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2)) = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre))) ”
  &&  emp
).

Definition query_return_wit_2_split_goal_1 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval_2: Z) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2)))) (PreH2 : (retval_2 <= retval)) (PreH3 : (retval <= (retval_2 + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ))) (PreH4 : (retval_2 = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH5 : (t_pre <= retval_2)) (PreH6 : (retval_2 <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH7 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH8 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH9 : (hi_pre > qr_pre)) (PreH10 : (ql_pre <= lo_pre)) (PreH11 : (NodeFits v_pre lo_pre hi_pre )) (PreH12 : (1 <= v_pre)) (PreH13 : (v_pre < 400020)) (PreH14 : (1 <= lo_pre)) (PreH15 : (lo_pre <= hi_pre)) (PreH16 : (hi_pre <= n)) (PreH17 : (n = (Zlength (arr)))) (PreH18 : (1 <= n)) (PreH19 : (n <= 100000)) (PreH20 : (1 <= ql_pre)) (PreH21 : (ql_pre <= qr_pre)) (PreH22 : (qr_pre <= n)) (PreH23 : (lo_pre <= qr_pre)) (PreH24 : (ql_pre <= hi_pre)) (PreH25 : (0 <= t_pre)) (PreH26 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH27 : (0 <= (t_pre % ( 60 ) ))) (PreH28 : ((t_pre % ( 60 ) ) < 60)) (PreH29 : (PeriodsOK arr )) (PreH30 : (CellsShaped cells )) (PreH31 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2)) <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ))
.

Definition query_return_wit_2_split_goal_2 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval_2: Z) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2)))) (PreH2 : (retval_2 <= retval)) (PreH3 : (retval <= (retval_2 + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ))) (PreH4 : (retval_2 = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH5 : (t_pre <= retval_2)) (PreH6 : (retval_2 <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH7 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH8 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH9 : (hi_pre > qr_pre)) (PreH10 : (ql_pre <= lo_pre)) (PreH11 : (NodeFits v_pre lo_pre hi_pre )) (PreH12 : (1 <= v_pre)) (PreH13 : (v_pre < 400020)) (PreH14 : (1 <= lo_pre)) (PreH15 : (lo_pre <= hi_pre)) (PreH16 : (hi_pre <= n)) (PreH17 : (n = (Zlength (arr)))) (PreH18 : (1 <= n)) (PreH19 : (n <= 100000)) (PreH20 : (1 <= ql_pre)) (PreH21 : (ql_pre <= qr_pre)) (PreH22 : (qr_pre <= n)) (PreH23 : (lo_pre <= qr_pre)) (PreH24 : (ql_pre <= hi_pre)) (PreH25 : (0 <= t_pre)) (PreH26 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH27 : (0 <= (t_pre % ( 60 ) ))) (PreH28 : ((t_pre % ( 60 ) ) < 60)) (PreH29 : (PeriodsOK arr )) (PreH30 : (CellsShaped cells )) (PreH31 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (t_pre <= (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2)))
.

Definition query_return_wit_2_split_goal_3 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval_2: Z) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2)))) (PreH2 : (retval_2 <= retval)) (PreH3 : (retval <= (retval_2 + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ))) (PreH4 : (retval_2 = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH5 : (t_pre <= retval_2)) (PreH6 : (retval_2 <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH7 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH8 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH9 : (hi_pre > qr_pre)) (PreH10 : (ql_pre <= lo_pre)) (PreH11 : (NodeFits v_pre lo_pre hi_pre )) (PreH12 : (1 <= v_pre)) (PreH13 : (v_pre < 400020)) (PreH14 : (1 <= lo_pre)) (PreH15 : (lo_pre <= hi_pre)) (PreH16 : (hi_pre <= n)) (PreH17 : (n = (Zlength (arr)))) (PreH18 : (1 <= n)) (PreH19 : (n <= 100000)) (PreH20 : (1 <= ql_pre)) (PreH21 : (ql_pre <= qr_pre)) (PreH22 : (qr_pre <= n)) (PreH23 : (lo_pre <= qr_pre)) (PreH24 : (ql_pre <= hi_pre)) (PreH25 : (0 <= t_pre)) (PreH26 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH27 : (0 <= (t_pre % ( 60 ) ))) (PreH28 : ((t_pre % ( 60 ) ) < 60)) (PreH29 : (PeriodsOK arr )) (PreH30 : (CellsShaped cells )) (PreH31 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (retval_2)) = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre)))
.

Definition query_return_wit_3 := 
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ))) (PreH4 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (ql_pre > lo_pre)) (PreH7 : (NodeFits v_pre lo_pre hi_pre )) (PreH8 : (1 <= v_pre)) (PreH9 : (v_pre < 400020)) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= hi_pre)) (PreH12 : (hi_pre <= n)) (PreH13 : (n = (Zlength (arr)))) (PreH14 : (1 <= n)) (PreH15 : (n <= 100000)) (PreH16 : (1 <= ql_pre)) (PreH17 : (ql_pre <= qr_pre)) (PreH18 : (qr_pre <= n)) (PreH19 : (lo_pre <= qr_pre)) (PreH20 : (ql_pre <= hi_pre)) (PreH21 : (0 <= t_pre)) (PreH22 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH23 : (0 <= (t_pre % ( 60 ) ))) (PreH24 : ((t_pre % ( 60 ) ) < 60)) (PreH25 : (PeriodsOK arr )) (PreH26 : (CellsShaped cells )) (PreH27 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (retval = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre))) ” 
  &&  “ (t_pre <= retval) ” 
  &&  “ (retval <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) )) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
) \/
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ))) (PreH4 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (ql_pre > lo_pre)) (PreH7 : (NodeFits v_pre lo_pre hi_pre )) (PreH8 : (1 <= v_pre)) (PreH9 : (v_pre < 400020)) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= hi_pre)) (PreH12 : (hi_pre <= n)) (PreH13 : (n = (Zlength (arr)))) (PreH14 : (1 <= n)) (PreH15 : (n <= 100000)) (PreH16 : (1 <= ql_pre)) (PreH17 : (ql_pre <= qr_pre)) (PreH18 : (qr_pre <= n)) (PreH19 : (lo_pre <= qr_pre)) (PreH20 : (ql_pre <= hi_pre)) (PreH21 : (0 <= t_pre)) (PreH22 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH23 : (0 <= (t_pre % ( 60 ) ))) (PreH24 : ((t_pre % ( 60 ) ) < 60)) (PreH25 : (PeriodsOK arr )) (PreH26 : (CellsShaped cells )) (PreH27 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  TT && emp 
|--
  “ (retval <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) )) ” 
  &&  “ (retval = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre))) ”
  &&  emp
).

Definition query_return_wit_3_split_goal_1 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ))) (PreH4 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (ql_pre > lo_pre)) (PreH7 : (NodeFits v_pre lo_pre hi_pre )) (PreH8 : (1 <= v_pre)) (PreH9 : (v_pre < 400020)) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= hi_pre)) (PreH12 : (hi_pre <= n)) (PreH13 : (n = (Zlength (arr)))) (PreH14 : (1 <= n)) (PreH15 : (n <= 100000)) (PreH16 : (1 <= ql_pre)) (PreH17 : (ql_pre <= qr_pre)) (PreH18 : (qr_pre <= n)) (PreH19 : (lo_pre <= qr_pre)) (PreH20 : (ql_pre <= hi_pre)) (PreH21 : (0 <= t_pre)) (PreH22 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH23 : (0 <= (t_pre % ( 60 ) ))) (PreH24 : ((t_pre % ( 60 ) ) < 60)) (PreH25 : (PeriodsOK arr )) (PreH26 : (CellsShaped cells )) (PreH27 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (retval <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ))
.

Definition query_return_wit_3_split_goal_2 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ))) (PreH4 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (ql_pre > lo_pre)) (PreH7 : (NodeFits v_pre lo_pre hi_pre )) (PreH8 : (1 <= v_pre)) (PreH9 : (v_pre < 400020)) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= hi_pre)) (PreH12 : (hi_pre <= n)) (PreH13 : (n = (Zlength (arr)))) (PreH14 : (1 <= n)) (PreH15 : (n <= 100000)) (PreH16 : (1 <= ql_pre)) (PreH17 : (ql_pre <= qr_pre)) (PreH18 : (qr_pre <= n)) (PreH19 : (lo_pre <= qr_pre)) (PreH20 : (ql_pre <= hi_pre)) (PreH21 : (0 <= t_pre)) (PreH22 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH23 : (0 <= (t_pre % ( 60 ) ))) (PreH24 : ((t_pre % ( 60 ) ) < 60)) (PreH25 : (PeriodsOK arr )) (PreH26 : (CellsShaped cells )) (PreH27 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (retval = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre)))
.

Definition query_return_wit_4 := 
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ))) (PreH4 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (hi_pre > qr_pre)) (PreH7 : (ql_pre <= lo_pre)) (PreH8 : (NodeFits v_pre lo_pre hi_pre )) (PreH9 : (1 <= v_pre)) (PreH10 : (v_pre < 400020)) (PreH11 : (1 <= lo_pre)) (PreH12 : (lo_pre <= hi_pre)) (PreH13 : (hi_pre <= n)) (PreH14 : (n = (Zlength (arr)))) (PreH15 : (1 <= n)) (PreH16 : (n <= 100000)) (PreH17 : (1 <= ql_pre)) (PreH18 : (ql_pre <= qr_pre)) (PreH19 : (qr_pre <= n)) (PreH20 : (lo_pre <= qr_pre)) (PreH21 : (ql_pre <= hi_pre)) (PreH22 : (0 <= t_pre)) (PreH23 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH24 : (0 <= (t_pre % ( 60 ) ))) (PreH25 : ((t_pre % ( 60 ) ) < 60)) (PreH26 : (PeriodsOK arr )) (PreH27 : (CellsShaped cells )) (PreH28 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (retval = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre))) ” 
  &&  “ (t_pre <= retval) ” 
  &&  “ (retval <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) )) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
) \/
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ))) (PreH4 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (hi_pre > qr_pre)) (PreH7 : (ql_pre <= lo_pre)) (PreH8 : (NodeFits v_pre lo_pre hi_pre )) (PreH9 : (1 <= v_pre)) (PreH10 : (v_pre < 400020)) (PreH11 : (1 <= lo_pre)) (PreH12 : (lo_pre <= hi_pre)) (PreH13 : (hi_pre <= n)) (PreH14 : (n = (Zlength (arr)))) (PreH15 : (1 <= n)) (PreH16 : (n <= 100000)) (PreH17 : (1 <= ql_pre)) (PreH18 : (ql_pre <= qr_pre)) (PreH19 : (qr_pre <= n)) (PreH20 : (lo_pre <= qr_pre)) (PreH21 : (ql_pre <= hi_pre)) (PreH22 : (0 <= t_pre)) (PreH23 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH24 : (0 <= (t_pre % ( 60 ) ))) (PreH25 : ((t_pre % ( 60 ) ) < 60)) (PreH26 : (PeriodsOK arr )) (PreH27 : (CellsShaped cells )) (PreH28 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  TT && emp 
|--
  “ (retval <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) )) ” 
  &&  “ (retval = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre))) ”
  &&  emp
).

Definition query_return_wit_4_split_goal_1 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ))) (PreH4 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (hi_pre > qr_pre)) (PreH7 : (ql_pre <= lo_pre)) (PreH8 : (NodeFits v_pre lo_pre hi_pre )) (PreH9 : (1 <= v_pre)) (PreH10 : (v_pre < 400020)) (PreH11 : (1 <= lo_pre)) (PreH12 : (lo_pre <= hi_pre)) (PreH13 : (hi_pre <= n)) (PreH14 : (n = (Zlength (arr)))) (PreH15 : (1 <= n)) (PreH16 : (n <= 100000)) (PreH17 : (1 <= ql_pre)) (PreH18 : (ql_pre <= qr_pre)) (PreH19 : (qr_pre <= n)) (PreH20 : (lo_pre <= qr_pre)) (PreH21 : (ql_pre <= hi_pre)) (PreH22 : (0 <= t_pre)) (PreH23 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH24 : (0 <= (t_pre % ( 60 ) ))) (PreH25 : ((t_pre % ( 60 ) ) < 60)) (PreH26 : (PeriodsOK arr )) (PreH27 : (CellsShaped cells )) (PreH28 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (retval <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ))
.

Definition query_return_wit_4_split_goal_2 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) ((((lo_pre + hi_pre ) ÷ 2 ) + 1 )) (hi_pre) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ))) (PreH4 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (hi_pre > qr_pre)) (PreH7 : (ql_pre <= lo_pre)) (PreH8 : (NodeFits v_pre lo_pre hi_pre )) (PreH9 : (1 <= v_pre)) (PreH10 : (v_pre < 400020)) (PreH11 : (1 <= lo_pre)) (PreH12 : (lo_pre <= hi_pre)) (PreH13 : (hi_pre <= n)) (PreH14 : (n = (Zlength (arr)))) (PreH15 : (1 <= n)) (PreH16 : (n <= 100000)) (PreH17 : (1 <= ql_pre)) (PreH18 : (ql_pre <= qr_pre)) (PreH19 : (qr_pre <= n)) (PreH20 : (lo_pre <= qr_pre)) (PreH21 : (ql_pre <= hi_pre)) (PreH22 : (0 <= t_pre)) (PreH23 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH24 : (0 <= (t_pre % ( 60 ) ))) (PreH25 : ((t_pre % ( 60 ) ) < 60)) (PreH26 : (PeriodsOK arr )) (PreH27 : (CellsShaped cells )) (PreH28 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (retval = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre)))
.

Definition query_return_wit_5 := 
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (ql_pre > lo_pre)) (PreH6 : (NodeFits v_pre lo_pre hi_pre )) (PreH7 : (1 <= v_pre)) (PreH8 : (v_pre < 400020)) (PreH9 : (1 <= lo_pre)) (PreH10 : (lo_pre <= hi_pre)) (PreH11 : (hi_pre <= n)) (PreH12 : (n = (Zlength (arr)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 100000)) (PreH15 : (1 <= ql_pre)) (PreH16 : (ql_pre <= qr_pre)) (PreH17 : (qr_pre <= n)) (PreH18 : (lo_pre <= qr_pre)) (PreH19 : (ql_pre <= hi_pre)) (PreH20 : (0 <= t_pre)) (PreH21 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH22 : (0 <= (t_pre % ( 60 ) ))) (PreH23 : ((t_pre % ( 60 ) ) < 60)) (PreH24 : (PeriodsOK arr )) (PreH25 : (CellsShaped cells )) (PreH26 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (retval = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre))) ” 
  &&  “ (t_pre <= retval) ” 
  &&  “ (retval <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) )) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
) \/
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (ql_pre > lo_pre)) (PreH6 : (NodeFits v_pre lo_pre hi_pre )) (PreH7 : (1 <= v_pre)) (PreH8 : (v_pre < 400020)) (PreH9 : (1 <= lo_pre)) (PreH10 : (lo_pre <= hi_pre)) (PreH11 : (hi_pre <= n)) (PreH12 : (n = (Zlength (arr)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 100000)) (PreH15 : (1 <= ql_pre)) (PreH16 : (ql_pre <= qr_pre)) (PreH17 : (qr_pre <= n)) (PreH18 : (lo_pre <= qr_pre)) (PreH19 : (ql_pre <= hi_pre)) (PreH20 : (0 <= t_pre)) (PreH21 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH22 : (0 <= (t_pre % ( 60 ) ))) (PreH23 : ((t_pre % ( 60 ) ) < 60)) (PreH24 : (PeriodsOK arr )) (PreH25 : (CellsShaped cells )) (PreH26 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  TT && emp 
|--
  “ (retval <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) )) ” 
  &&  “ (retval = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre))) ”
  &&  emp
).

Definition query_return_wit_5_split_goal_1 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (ql_pre > lo_pre)) (PreH6 : (NodeFits v_pre lo_pre hi_pre )) (PreH7 : (1 <= v_pre)) (PreH8 : (v_pre < 400020)) (PreH9 : (1 <= lo_pre)) (PreH10 : (lo_pre <= hi_pre)) (PreH11 : (hi_pre <= n)) (PreH12 : (n = (Zlength (arr)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 100000)) (PreH15 : (1 <= ql_pre)) (PreH16 : (ql_pre <= qr_pre)) (PreH17 : (qr_pre <= n)) (PreH18 : (lo_pre <= qr_pre)) (PreH19 : (ql_pre <= hi_pre)) (PreH20 : (0 <= t_pre)) (PreH21 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH22 : (0 <= (t_pre % ( 60 ) ))) (PreH23 : ((t_pre % ( 60 ) ) < 60)) (PreH24 : (PeriodsOK arr )) (PreH25 : (CellsShaped cells )) (PreH26 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (retval <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ))
.

Definition query_return_wit_5_split_goal_2 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (ql_pre > lo_pre)) (PreH6 : (NodeFits v_pre lo_pre hi_pre )) (PreH7 : (1 <= v_pre)) (PreH8 : (v_pre < 400020)) (PreH9 : (1 <= lo_pre)) (PreH10 : (lo_pre <= hi_pre)) (PreH11 : (hi_pre <= n)) (PreH12 : (n = (Zlength (arr)))) (PreH13 : (1 <= n)) (PreH14 : (n <= 100000)) (PreH15 : (1 <= ql_pre)) (PreH16 : (ql_pre <= qr_pre)) (PreH17 : (qr_pre <= n)) (PreH18 : (lo_pre <= qr_pre)) (PreH19 : (ql_pre <= hi_pre)) (PreH20 : (0 <= t_pre)) (PreH21 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH22 : (0 <= (t_pre % ( 60 ) ))) (PreH23 : ((t_pre % ( 60 ) ) < 60)) (PreH24 : (PeriodsOK arr )) (PreH25 : (CellsShaped cells )) (PreH26 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (retval = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre)))
.

Definition query_return_wit_6 := 
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (hi_pre > qr_pre)) (PreH6 : (ql_pre <= lo_pre)) (PreH7 : (NodeFits v_pre lo_pre hi_pre )) (PreH8 : (1 <= v_pre)) (PreH9 : (v_pre < 400020)) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= hi_pre)) (PreH12 : (hi_pre <= n)) (PreH13 : (n = (Zlength (arr)))) (PreH14 : (1 <= n)) (PreH15 : (n <= 100000)) (PreH16 : (1 <= ql_pre)) (PreH17 : (ql_pre <= qr_pre)) (PreH18 : (qr_pre <= n)) (PreH19 : (lo_pre <= qr_pre)) (PreH20 : (ql_pre <= hi_pre)) (PreH21 : (0 <= t_pre)) (PreH22 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH23 : (0 <= (t_pre % ( 60 ) ))) (PreH24 : ((t_pre % ( 60 ) ) < 60)) (PreH25 : (PeriodsOK arr )) (PreH26 : (CellsShaped cells )) (PreH27 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (retval = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre))) ” 
  &&  “ (t_pre <= retval) ” 
  &&  “ (retval <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) )) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
) \/
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (hi_pre > qr_pre)) (PreH6 : (ql_pre <= lo_pre)) (PreH7 : (NodeFits v_pre lo_pre hi_pre )) (PreH8 : (1 <= v_pre)) (PreH9 : (v_pre < 400020)) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= hi_pre)) (PreH12 : (hi_pre <= n)) (PreH13 : (n = (Zlength (arr)))) (PreH14 : (1 <= n)) (PreH15 : (n <= 100000)) (PreH16 : (1 <= ql_pre)) (PreH17 : (ql_pre <= qr_pre)) (PreH18 : (qr_pre <= n)) (PreH19 : (lo_pre <= qr_pre)) (PreH20 : (ql_pre <= hi_pre)) (PreH21 : (0 <= t_pre)) (PreH22 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH23 : (0 <= (t_pre % ( 60 ) ))) (PreH24 : ((t_pre % ( 60 ) ) < 60)) (PreH25 : (PeriodsOK arr )) (PreH26 : (CellsShaped cells )) (PreH27 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  TT && emp 
|--
  “ (retval <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) )) ” 
  &&  “ (retval = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre))) ”
  &&  emp
).

Definition query_return_wit_6_split_goal_1 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (hi_pre > qr_pre)) (PreH6 : (ql_pre <= lo_pre)) (PreH7 : (NodeFits v_pre lo_pre hi_pre )) (PreH8 : (1 <= v_pre)) (PreH9 : (v_pre < 400020)) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= hi_pre)) (PreH12 : (hi_pre <= n)) (PreH13 : (n = (Zlength (arr)))) (PreH14 : (1 <= n)) (PreH15 : (n <= 100000)) (PreH16 : (1 <= ql_pre)) (PreH17 : (ql_pre <= qr_pre)) (PreH18 : (qr_pre <= n)) (PreH19 : (lo_pre <= qr_pre)) (PreH20 : (ql_pre <= hi_pre)) (PreH21 : (0 <= t_pre)) (PreH22 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH23 : (0 <= (t_pre % ( 60 ) ))) (PreH24 : ((t_pre % ( 60 ) ) < 60)) (PreH25 : (PeriodsOK arr )) (PreH26 : (CellsShaped cells )) (PreH27 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (retval <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ))
.

Definition query_return_wit_6_split_goal_2 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (hi_pre > qr_pre)) (PreH6 : (ql_pre <= lo_pre)) (PreH7 : (NodeFits v_pre lo_pre hi_pre )) (PreH8 : (1 <= v_pre)) (PreH9 : (v_pre < 400020)) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= hi_pre)) (PreH12 : (hi_pre <= n)) (PreH13 : (n = (Zlength (arr)))) (PreH14 : (1 <= n)) (PreH15 : (n <= 100000)) (PreH16 : (1 <= ql_pre)) (PreH17 : (ql_pre <= qr_pre)) (PreH18 : (qr_pre <= n)) (PreH19 : (lo_pre <= qr_pre)) (PreH20 : (ql_pre <= hi_pre)) (PreH21 : (0 <= t_pre)) (PreH22 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH23 : (0 <= (t_pre % ( 60 ) ))) (PreH24 : ((t_pre % ( 60 ) ) < 60)) (PreH25 : (PeriodsOK arr )) (PreH26 : (CellsShaped cells )) (PreH27 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (retval = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre)))
.

Definition query_return_wit_7 := 
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z))))  __default__List__App_option_Z (PreH1 : (hi_pre <= qr_pre)) (PreH2 : (ql_pre <= lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (v_pre) ((replace_Znth ((t_pre % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) )))))) ((Znth v_pre cells __default__List__App_option_Z)))) (cells)) )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
|--
  “ ((t_pre + (Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) ))) ) = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre))) ” 
  &&  “ (t_pre <= (t_pre + (Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) ))) )) ” 
  &&  “ ((t_pre + (Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) ))) ) <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) )) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
) \/
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z))))  __default__List__App_option_Z (PreH1 : (hi_pre <= qr_pre)) (PreH2 : (ql_pre <= lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (v_pre) ((replace_Znth ((t_pre % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) )))))) ((Znth v_pre cells __default__List__App_option_Z)))) (cells)) )
|--
  “ ((t_pre + (Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) ))) ) <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) )) ” 
  &&  “ (t_pre <= (t_pre + (Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) ))) )) ” 
  &&  “ ((t_pre + (Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) ))) ) = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre))) ”
  &&  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
).

Definition query_return_wit_7_split_goal_1 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z))))  __default__List__App_option_Z (PreH1 : (hi_pre <= qr_pre)) (PreH2 : (ql_pre <= lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (v_pre) ((replace_Znth ((t_pre % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) )))))) ((Znth v_pre cells __default__List__App_option_Z)))) (cells)) )
|--
  “ ((t_pre + (Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) ))) ) <= (t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) )) ”
.

Definition query_return_wit_7_split_goal_2 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z))))  __default__List__App_option_Z (PreH1 : (hi_pre <= qr_pre)) (PreH2 : (ql_pre <= lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (v_pre) ((replace_Znth ((t_pre % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) )))))) ((Znth v_pre cells __default__List__App_option_Z)))) (cells)) )
|--
  “ (t_pre <= (t_pre + (Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) ))) )) ”
.

Definition query_return_wit_7_split_goal_3 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z))))  __default__List__App_option_Z (PreH1 : (hi_pre <= qr_pre)) (PreH2 : (ql_pre <= lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (v_pre) ((replace_Znth ((t_pre % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) )))))) ((Znth v_pre cells __default__List__App_option_Z)))) (cells)) )
|--
  “ ((t_pre + (Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) ))) ) = (cross ((QuerySlice (arr) (lo_pre) (hi_pre) (ql_pre) (qr_pre))) (t_pre))) ”
.

Definition query_return_wit_7_split_goal_spatial := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z))))  __default__List__App_option_Z (PreH1 : (hi_pre <= qr_pre)) (PreH2 : (ql_pre <= lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 (Array2.replace_mixed_row (v_pre) ((replace_Znth ((t_pre % ( 60 ) )) ((Some ((Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) )))))) ((Znth v_pre cells __default__List__App_option_Z)))) (cells)) )
|--
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
.

Definition query_partial_solve_wit_1_pure := 
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z))))  __default__List__App_option_Z (PreH1 : (hi_pre <= qr_pre)) (PreH2 : (ql_pre <= lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (Array2.mixed_def (Znth v_pre cells __default__List__App_option_Z) (t_pre % ( 60 ) ) ) ”
) \/
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z))))  __default__List__App_option_Z (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (t_pre >= INT_MIN)) (PreH8 : (qr_pre >= INT_MIN)) (PreH9 : (ql_pre >= INT_MIN)) (PreH10 : (hi_pre >= INT_MIN)) (PreH11 : (lo_pre >= INT_MIN)) (PreH12 : (v_pre >= INT_MIN)) (PreH13 : (hi_pre <= qr_pre)) (PreH14 : (ql_pre <= lo_pre)) (PreH15 : (NodeFits v_pre lo_pre hi_pre )) (PreH16 : (1 <= v_pre)) (PreH17 : (v_pre < 400020)) (PreH18 : (1 <= lo_pre)) (PreH19 : (lo_pre <= hi_pre)) (PreH20 : (hi_pre <= n)) (PreH21 : (n = (Zlength (arr)))) (PreH22 : (1 <= n)) (PreH23 : (n <= 100000)) (PreH24 : (1 <= ql_pre)) (PreH25 : (ql_pre <= qr_pre)) (PreH26 : (qr_pre <= n)) (PreH27 : (lo_pre <= qr_pre)) (PreH28 : (ql_pre <= hi_pre)) (PreH29 : (0 <= t_pre)) (PreH30 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH31 : (0 <= (t_pre % ( 60 ) ))) (PreH32 : ((t_pre % ( 60 ) ) < 60)) (PreH33 : (PeriodsOK arr )) (PreH34 : (CellsShaped cells )) (PreH35 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (Array2.mixed_def (Znth v_pre cells __default__List__App_option_Z) (t_pre % ( 60 ) ) ) ”
).

Definition query_partial_solve_wit_1_pure_split_goal_1 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z))))  __default__List__App_option_Z (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (t_pre >= INT_MIN)) (PreH8 : (qr_pre >= INT_MIN)) (PreH9 : (ql_pre >= INT_MIN)) (PreH10 : (hi_pre >= INT_MIN)) (PreH11 : (lo_pre >= INT_MIN)) (PreH12 : (v_pre >= INT_MIN)) (PreH13 : (hi_pre <= qr_pre)) (PreH14 : (ql_pre <= lo_pre)) (PreH15 : (NodeFits v_pre lo_pre hi_pre )) (PreH16 : (1 <= v_pre)) (PreH17 : (v_pre < 400020)) (PreH18 : (1 <= lo_pre)) (PreH19 : (lo_pre <= hi_pre)) (PreH20 : (hi_pre <= n)) (PreH21 : (n = (Zlength (arr)))) (PreH22 : (1 <= n)) (PreH23 : (n <= 100000)) (PreH24 : (1 <= ql_pre)) (PreH25 : (ql_pre <= qr_pre)) (PreH26 : (qr_pre <= n)) (PreH27 : (lo_pre <= qr_pre)) (PreH28 : (ql_pre <= hi_pre)) (PreH29 : (0 <= t_pre)) (PreH30 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH31 : (0 <= (t_pre % ( 60 ) ))) (PreH32 : ((t_pre % ( 60 ) ) < 60)) (PreH33 : (PeriodsOK arr )) (PreH34 : (CellsShaped cells )) (PreH35 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (Array2.mixed_def (Znth v_pre cells __default__List__App_option_Z) (t_pre % ( 60 ) ) ) ”
.

Definition query_partial_solve_wit_1_aux := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z))))  __default__List__App_option_Z (PreH1 : (hi_pre <= qr_pre)) (PreH2 : (ql_pre <= lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (Array2.mixed_def (Znth v_pre cells __default__List__App_option_Z) (t_pre % ( 60 ) ) ) ” 
  &&  “ (hi_pre <= qr_pre) ” 
  &&  “ (ql_pre <= lo_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ (lo_pre <= qr_pre) ” 
  &&  “ (ql_pre <= hi_pre) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (0 <= (t_pre % ( 60 ) )) ” 
  &&  “ ((t_pre % ( 60 ) ) < 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr v_pre lo_pre hi_pre ) ”
  &&  ((((( &( "seg" ) ) + (v_pre * (sizeof(INT) * 60))) + ((t_pre % ( 60 ) ) * sizeof(INT)))) # Int  |-> (Array2.mixed_val ((Znth v_pre cells __default__List__App_option_Z)) ((t_pre % ( 60 ) ))))
  **  (IntArray.mixed_missing_i (( &( "seg" ) ) + (v_pre * (sizeof(INT) * 60))) (t_pre % ( 60 ) ) 0 60 (Znth v_pre cells __default__List__App_option_Z) )
  **  (IntArray2.mixed_missing_i ( &( "seg" ) ) v_pre 0 400020 60 cells )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
.

Definition query_partial_solve_wit_1 := query_partial_solve_wit_1_pure -> query_partial_solve_wit_1_aux.

Definition query_partial_solve_wit_2_pure := 
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (ql_pre > lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ (lo_pre <= qr_pre) ” 
  &&  “ (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ ((t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (((lo_pre + hi_pre ) ÷ 2 ) <= n) ” 
  &&  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ”
) \/
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (ql_pre > lo_pre)) (PreH17 : (NodeFits v_pre lo_pre hi_pre )) (PreH18 : (1 <= v_pre)) (PreH19 : (v_pre < 400020)) (PreH20 : (1 <= lo_pre)) (PreH21 : (lo_pre <= hi_pre)) (PreH22 : (hi_pre <= n)) (PreH23 : (n = (Zlength (arr)))) (PreH24 : (1 <= n)) (PreH25 : (n <= 100000)) (PreH26 : (1 <= ql_pre)) (PreH27 : (ql_pre <= qr_pre)) (PreH28 : (qr_pre <= n)) (PreH29 : (lo_pre <= qr_pre)) (PreH30 : (ql_pre <= hi_pre)) (PreH31 : (0 <= t_pre)) (PreH32 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH33 : (0 <= (t_pre % ( 60 ) ))) (PreH34 : ((t_pre % ( 60 ) ) < 60)) (PreH35 : (PeriodsOK arr )) (PreH36 : (CellsShaped cells )) (PreH37 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ (((lo_pre + hi_pre ) ÷ 2 ) <= n) ” 
  &&  “ ((t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (TreeOK cells arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ”
).

Definition query_partial_solve_wit_2_pure_split_goal_1 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (ql_pre > lo_pre)) (PreH17 : (NodeFits v_pre lo_pre hi_pre )) (PreH18 : (1 <= v_pre)) (PreH19 : (v_pre < 400020)) (PreH20 : (1 <= lo_pre)) (PreH21 : (lo_pre <= hi_pre)) (PreH22 : (hi_pre <= n)) (PreH23 : (n = (Zlength (arr)))) (PreH24 : (1 <= n)) (PreH25 : (n <= 100000)) (PreH26 : (1 <= ql_pre)) (PreH27 : (ql_pre <= qr_pre)) (PreH28 : (qr_pre <= n)) (PreH29 : (lo_pre <= qr_pre)) (PreH30 : (ql_pre <= hi_pre)) (PreH31 : (0 <= t_pre)) (PreH32 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH33 : (0 <= (t_pre % ( 60 ) ))) (PreH34 : ((t_pre % ( 60 ) ) < 60)) (PreH35 : (PeriodsOK arr )) (PreH36 : (CellsShaped cells )) (PreH37 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ”
.

Definition query_partial_solve_wit_2_pure_split_goal_2 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (ql_pre > lo_pre)) (PreH17 : (NodeFits v_pre lo_pre hi_pre )) (PreH18 : (1 <= v_pre)) (PreH19 : (v_pre < 400020)) (PreH20 : (1 <= lo_pre)) (PreH21 : (lo_pre <= hi_pre)) (PreH22 : (hi_pre <= n)) (PreH23 : (n = (Zlength (arr)))) (PreH24 : (1 <= n)) (PreH25 : (n <= 100000)) (PreH26 : (1 <= ql_pre)) (PreH27 : (ql_pre <= qr_pre)) (PreH28 : (qr_pre <= n)) (PreH29 : (lo_pre <= qr_pre)) (PreH30 : (ql_pre <= hi_pre)) (PreH31 : (0 <= t_pre)) (PreH32 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH33 : (0 <= (t_pre % ( 60 ) ))) (PreH34 : ((t_pre % ( 60 ) ) < 60)) (PreH35 : (PeriodsOK arr )) (PreH36 : (CellsShaped cells )) (PreH37 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (((lo_pre + hi_pre ) ÷ 2 ) <= n) ”
.

Definition query_partial_solve_wit_2_pure_split_goal_3 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (ql_pre > lo_pre)) (PreH17 : (NodeFits v_pre lo_pre hi_pre )) (PreH18 : (1 <= v_pre)) (PreH19 : (v_pre < 400020)) (PreH20 : (1 <= lo_pre)) (PreH21 : (lo_pre <= hi_pre)) (PreH22 : (hi_pre <= n)) (PreH23 : (n = (Zlength (arr)))) (PreH24 : (1 <= n)) (PreH25 : (n <= 100000)) (PreH26 : (1 <= ql_pre)) (PreH27 : (ql_pre <= qr_pre)) (PreH28 : (qr_pre <= n)) (PreH29 : (lo_pre <= qr_pre)) (PreH30 : (ql_pre <= hi_pre)) (PreH31 : (0 <= t_pre)) (PreH32 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH33 : (0 <= (t_pre % ( 60 ) ))) (PreH34 : ((t_pre % ( 60 ) ) < 60)) (PreH35 : (PeriodsOK arr )) (PreH36 : (CellsShaped cells )) (PreH37 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ) <= 400000) ”
.

Definition query_partial_solve_wit_2_pure_split_goal_4 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (ql_pre > lo_pre)) (PreH17 : (NodeFits v_pre lo_pre hi_pre )) (PreH18 : (1 <= v_pre)) (PreH19 : (v_pre < 400020)) (PreH20 : (1 <= lo_pre)) (PreH21 : (lo_pre <= hi_pre)) (PreH22 : (hi_pre <= n)) (PreH23 : (n = (Zlength (arr)))) (PreH24 : (1 <= n)) (PreH25 : (n <= 100000)) (PreH26 : (1 <= ql_pre)) (PreH27 : (ql_pre <= qr_pre)) (PreH28 : (qr_pre <= n)) (PreH29 : (lo_pre <= qr_pre)) (PreH30 : (ql_pre <= hi_pre)) (PreH31 : (0 <= t_pre)) (PreH32 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH33 : (0 <= (t_pre % ( 60 ) ))) (PreH34 : ((t_pre % ( 60 ) ) < 60)) (PreH35 : (PeriodsOK arr )) (PreH36 : (CellsShaped cells )) (PreH37 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (TreeOK cells arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ”
.

Definition query_partial_solve_wit_2_aux := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (ql_pre > lo_pre)) (PreH3 : (NodeFits v_pre lo_pre hi_pre )) (PreH4 : (1 <= v_pre)) (PreH5 : (v_pre < 400020)) (PreH6 : (1 <= lo_pre)) (PreH7 : (lo_pre <= hi_pre)) (PreH8 : (hi_pre <= n)) (PreH9 : (n = (Zlength (arr)))) (PreH10 : (1 <= n)) (PreH11 : (n <= 100000)) (PreH12 : (1 <= ql_pre)) (PreH13 : (ql_pre <= qr_pre)) (PreH14 : (qr_pre <= n)) (PreH15 : (lo_pre <= qr_pre)) (PreH16 : (ql_pre <= hi_pre)) (PreH17 : (0 <= t_pre)) (PreH18 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH19 : (0 <= (t_pre % ( 60 ) ))) (PreH20 : ((t_pre % ( 60 ) ) < 60)) (PreH21 : (PeriodsOK arr )) (PreH22 : (CellsShaped cells )) (PreH23 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ (lo_pre <= qr_pre) ” 
  &&  “ (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ ((t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (((lo_pre + hi_pre ) ÷ 2 ) <= n) ” 
  &&  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (ql_pre > lo_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ (lo_pre <= qr_pre) ” 
  &&  “ (ql_pre <= hi_pre) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (0 <= (t_pre % ( 60 ) )) ” 
  &&  “ ((t_pre % ( 60 ) ) < 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr v_pre lo_pre hi_pre ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
.

Definition query_partial_solve_wit_2 := query_partial_solve_wit_2_pure -> query_partial_solve_wit_2_aux.

Definition query_partial_solve_wit_3_pure := 
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (hi_pre > qr_pre)) (PreH3 : (ql_pre <= lo_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= hi_pre)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (1 <= ql_pre)) (PreH14 : (ql_pre <= qr_pre)) (PreH15 : (qr_pre <= n)) (PreH16 : (lo_pre <= qr_pre)) (PreH17 : (ql_pre <= hi_pre)) (PreH18 : (0 <= t_pre)) (PreH19 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH20 : (0 <= (t_pre % ( 60 ) ))) (PreH21 : ((t_pre % ( 60 ) ) < 60)) (PreH22 : (PeriodsOK arr )) (PreH23 : (CellsShaped cells )) (PreH24 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ (lo_pre <= qr_pre) ” 
  &&  “ (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ ((t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (((lo_pre + hi_pre ) ÷ 2 ) <= n) ” 
  &&  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ”
) \/
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (hi_pre > qr_pre)) (PreH17 : (ql_pre <= lo_pre)) (PreH18 : (NodeFits v_pre lo_pre hi_pre )) (PreH19 : (1 <= v_pre)) (PreH20 : (v_pre < 400020)) (PreH21 : (1 <= lo_pre)) (PreH22 : (lo_pre <= hi_pre)) (PreH23 : (hi_pre <= n)) (PreH24 : (n = (Zlength (arr)))) (PreH25 : (1 <= n)) (PreH26 : (n <= 100000)) (PreH27 : (1 <= ql_pre)) (PreH28 : (ql_pre <= qr_pre)) (PreH29 : (qr_pre <= n)) (PreH30 : (lo_pre <= qr_pre)) (PreH31 : (ql_pre <= hi_pre)) (PreH32 : (0 <= t_pre)) (PreH33 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH34 : (0 <= (t_pre % ( 60 ) ))) (PreH35 : ((t_pre % ( 60 ) ) < 60)) (PreH36 : (PeriodsOK arr )) (PreH37 : (CellsShaped cells )) (PreH38 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ (((lo_pre + hi_pre ) ÷ 2 ) <= n) ” 
  &&  “ ((t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (TreeOK cells arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ”
).

Definition query_partial_solve_wit_3_pure_split_goal_1 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (hi_pre > qr_pre)) (PreH17 : (ql_pre <= lo_pre)) (PreH18 : (NodeFits v_pre lo_pre hi_pre )) (PreH19 : (1 <= v_pre)) (PreH20 : (v_pre < 400020)) (PreH21 : (1 <= lo_pre)) (PreH22 : (lo_pre <= hi_pre)) (PreH23 : (hi_pre <= n)) (PreH24 : (n = (Zlength (arr)))) (PreH25 : (1 <= n)) (PreH26 : (n <= 100000)) (PreH27 : (1 <= ql_pre)) (PreH28 : (ql_pre <= qr_pre)) (PreH29 : (qr_pre <= n)) (PreH30 : (lo_pre <= qr_pre)) (PreH31 : (ql_pre <= hi_pre)) (PreH32 : (0 <= t_pre)) (PreH33 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH34 : (0 <= (t_pre % ( 60 ) ))) (PreH35 : ((t_pre % ( 60 ) ) < 60)) (PreH36 : (PeriodsOK arr )) (PreH37 : (CellsShaped cells )) (PreH38 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ”
.

Definition query_partial_solve_wit_3_pure_split_goal_2 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (hi_pre > qr_pre)) (PreH17 : (ql_pre <= lo_pre)) (PreH18 : (NodeFits v_pre lo_pre hi_pre )) (PreH19 : (1 <= v_pre)) (PreH20 : (v_pre < 400020)) (PreH21 : (1 <= lo_pre)) (PreH22 : (lo_pre <= hi_pre)) (PreH23 : (hi_pre <= n)) (PreH24 : (n = (Zlength (arr)))) (PreH25 : (1 <= n)) (PreH26 : (n <= 100000)) (PreH27 : (1 <= ql_pre)) (PreH28 : (ql_pre <= qr_pre)) (PreH29 : (qr_pre <= n)) (PreH30 : (lo_pre <= qr_pre)) (PreH31 : (ql_pre <= hi_pre)) (PreH32 : (0 <= t_pre)) (PreH33 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH34 : (0 <= (t_pre % ( 60 ) ))) (PreH35 : ((t_pre % ( 60 ) ) < 60)) (PreH36 : (PeriodsOK arr )) (PreH37 : (CellsShaped cells )) (PreH38 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (((lo_pre + hi_pre ) ÷ 2 ) <= n) ”
.

Definition query_partial_solve_wit_3_pure_split_goal_3 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (hi_pre > qr_pre)) (PreH17 : (ql_pre <= lo_pre)) (PreH18 : (NodeFits v_pre lo_pre hi_pre )) (PreH19 : (1 <= v_pre)) (PreH20 : (v_pre < 400020)) (PreH21 : (1 <= lo_pre)) (PreH22 : (lo_pre <= hi_pre)) (PreH23 : (hi_pre <= n)) (PreH24 : (n = (Zlength (arr)))) (PreH25 : (1 <= n)) (PreH26 : (n <= 100000)) (PreH27 : (1 <= ql_pre)) (PreH28 : (ql_pre <= qr_pre)) (PreH29 : (qr_pre <= n)) (PreH30 : (lo_pre <= qr_pre)) (PreH31 : (ql_pre <= hi_pre)) (PreH32 : (0 <= t_pre)) (PreH33 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH34 : (0 <= (t_pre % ( 60 ) ))) (PreH35 : ((t_pre % ( 60 ) ) < 60)) (PreH36 : (PeriodsOK arr )) (PreH37 : (CellsShaped cells )) (PreH38 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ) <= 400000) ”
.

Definition query_partial_solve_wit_3_pure_split_goal_4 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (hi_pre > qr_pre)) (PreH17 : (ql_pre <= lo_pre)) (PreH18 : (NodeFits v_pre lo_pre hi_pre )) (PreH19 : (1 <= v_pre)) (PreH20 : (v_pre < 400020)) (PreH21 : (1 <= lo_pre)) (PreH22 : (lo_pre <= hi_pre)) (PreH23 : (hi_pre <= n)) (PreH24 : (n = (Zlength (arr)))) (PreH25 : (1 <= n)) (PreH26 : (n <= 100000)) (PreH27 : (1 <= ql_pre)) (PreH28 : (ql_pre <= qr_pre)) (PreH29 : (qr_pre <= n)) (PreH30 : (lo_pre <= qr_pre)) (PreH31 : (ql_pre <= hi_pre)) (PreH32 : (0 <= t_pre)) (PreH33 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH34 : (0 <= (t_pre % ( 60 ) ))) (PreH35 : ((t_pre % ( 60 ) ) < 60)) (PreH36 : (PeriodsOK arr )) (PreH37 : (CellsShaped cells )) (PreH38 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (TreeOK cells arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ”
.

Definition query_partial_solve_wit_3_aux := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (hi_pre > qr_pre)) (PreH3 : (ql_pre <= lo_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= hi_pre)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (1 <= ql_pre)) (PreH14 : (ql_pre <= qr_pre)) (PreH15 : (qr_pre <= n)) (PreH16 : (lo_pre <= qr_pre)) (PreH17 : (ql_pre <= hi_pre)) (PreH18 : (0 <= t_pre)) (PreH19 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH20 : (0 <= (t_pre % ( 60 ) ))) (PreH21 : ((t_pre % ( 60 ) ) < 60)) (PreH22 : (PeriodsOK arr )) (PreH23 : (CellsShaped cells )) (PreH24 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ (lo_pre <= qr_pre) ” 
  &&  “ (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ ((t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (((lo_pre + hi_pre ) ÷ 2 ) <= n) ” 
  &&  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ (qr_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (hi_pre > qr_pre) ” 
  &&  “ (ql_pre <= lo_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ (lo_pre <= qr_pre) ” 
  &&  “ (ql_pre <= hi_pre) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (0 <= (t_pre % ( 60 ) )) ” 
  &&  “ ((t_pre % ( 60 ) ) < 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr v_pre lo_pre hi_pre ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
.

Definition query_partial_solve_wit_3 := query_partial_solve_wit_3_pure -> query_partial_solve_wit_3_aux.

Definition query_partial_solve_wit_4_pure := 
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (ql_pre > lo_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= hi_pre)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (1 <= ql_pre)) (PreH14 : (ql_pre <= qr_pre)) (PreH15 : (qr_pre <= n)) (PreH16 : (lo_pre <= qr_pre)) (PreH17 : (ql_pre <= hi_pre)) (PreH18 : (0 <= t_pre)) (PreH19 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH20 : (0 <= (t_pre % ( 60 ) ))) (PreH21 : ((t_pre % ( 60 ) ) < 60)) (PreH22 : (PeriodsOK arr )) (PreH23 : (CellsShaped cells )) (PreH24 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ ((((lo_pre + hi_pre ) ÷ 2 ) + 1 ) <= qr_pre) ” 
  &&  “ (ql_pre <= hi_pre) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ ((t_pre + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ) <= 400000) ” 
  &&  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
) \/
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH17 : (ql_pre > lo_pre)) (PreH18 : (NodeFits v_pre lo_pre hi_pre )) (PreH19 : (1 <= v_pre)) (PreH20 : (v_pre < 400020)) (PreH21 : (1 <= lo_pre)) (PreH22 : (lo_pre <= hi_pre)) (PreH23 : (hi_pre <= n)) (PreH24 : (n = (Zlength (arr)))) (PreH25 : (1 <= n)) (PreH26 : (n <= 100000)) (PreH27 : (1 <= ql_pre)) (PreH28 : (ql_pre <= qr_pre)) (PreH29 : (qr_pre <= n)) (PreH30 : (lo_pre <= qr_pre)) (PreH31 : (ql_pre <= hi_pre)) (PreH32 : (0 <= t_pre)) (PreH33 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH34 : (0 <= (t_pre % ( 60 ) ))) (PreH35 : ((t_pre % ( 60 ) ) < 60)) (PreH36 : (PeriodsOK arr )) (PreH37 : (CellsShaped cells )) (PreH38 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ ((t_pre + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ) <= 400000) ” 
  &&  “ (TreeOK cells arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
).

Definition query_partial_solve_wit_4_pure_split_goal_1 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH17 : (ql_pre > lo_pre)) (PreH18 : (NodeFits v_pre lo_pre hi_pre )) (PreH19 : (1 <= v_pre)) (PreH20 : (v_pre < 400020)) (PreH21 : (1 <= lo_pre)) (PreH22 : (lo_pre <= hi_pre)) (PreH23 : (hi_pre <= n)) (PreH24 : (n = (Zlength (arr)))) (PreH25 : (1 <= n)) (PreH26 : (n <= 100000)) (PreH27 : (1 <= ql_pre)) (PreH28 : (ql_pre <= qr_pre)) (PreH29 : (qr_pre <= n)) (PreH30 : (lo_pre <= qr_pre)) (PreH31 : (ql_pre <= hi_pre)) (PreH32 : (0 <= t_pre)) (PreH33 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH34 : (0 <= (t_pre % ( 60 ) ))) (PreH35 : ((t_pre % ( 60 ) ) < 60)) (PreH36 : (PeriodsOK arr )) (PreH37 : (CellsShaped cells )) (PreH38 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
.

Definition query_partial_solve_wit_4_pure_split_goal_2 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH17 : (ql_pre > lo_pre)) (PreH18 : (NodeFits v_pre lo_pre hi_pre )) (PreH19 : (1 <= v_pre)) (PreH20 : (v_pre < 400020)) (PreH21 : (1 <= lo_pre)) (PreH22 : (lo_pre <= hi_pre)) (PreH23 : (hi_pre <= n)) (PreH24 : (n = (Zlength (arr)))) (PreH25 : (1 <= n)) (PreH26 : (n <= 100000)) (PreH27 : (1 <= ql_pre)) (PreH28 : (ql_pre <= qr_pre)) (PreH29 : (qr_pre <= n)) (PreH30 : (lo_pre <= qr_pre)) (PreH31 : (ql_pre <= hi_pre)) (PreH32 : (0 <= t_pre)) (PreH33 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH34 : (0 <= (t_pre % ( 60 ) ))) (PreH35 : ((t_pre % ( 60 ) ) < 60)) (PreH36 : (PeriodsOK arr )) (PreH37 : (CellsShaped cells )) (PreH38 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((t_pre + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ) <= 400000) ”
.

Definition query_partial_solve_wit_4_pure_split_goal_3 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH17 : (ql_pre > lo_pre)) (PreH18 : (NodeFits v_pre lo_pre hi_pre )) (PreH19 : (1 <= v_pre)) (PreH20 : (v_pre < 400020)) (PreH21 : (1 <= lo_pre)) (PreH22 : (lo_pre <= hi_pre)) (PreH23 : (hi_pre <= n)) (PreH24 : (n = (Zlength (arr)))) (PreH25 : (1 <= n)) (PreH26 : (n <= 100000)) (PreH27 : (1 <= ql_pre)) (PreH28 : (ql_pre <= qr_pre)) (PreH29 : (qr_pre <= n)) (PreH30 : (lo_pre <= qr_pre)) (PreH31 : (ql_pre <= hi_pre)) (PreH32 : (0 <= t_pre)) (PreH33 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH34 : (0 <= (t_pre % ( 60 ) ))) (PreH35 : ((t_pre % ( 60 ) ) < 60)) (PreH36 : (PeriodsOK arr )) (PreH37 : (CellsShaped cells )) (PreH38 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (TreeOK cells arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
.

Definition query_partial_solve_wit_4_aux := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (ql_pre > lo_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= hi_pre)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (1 <= ql_pre)) (PreH14 : (ql_pre <= qr_pre)) (PreH15 : (qr_pre <= n)) (PreH16 : (lo_pre <= qr_pre)) (PreH17 : (ql_pre <= hi_pre)) (PreH18 : (0 <= t_pre)) (PreH19 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH20 : (0 <= (t_pre % ( 60 ) ))) (PreH21 : ((t_pre % ( 60 ) ) < 60)) (PreH22 : (PeriodsOK arr )) (PreH23 : (CellsShaped cells )) (PreH24 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ ((((lo_pre + hi_pre ) ÷ 2 ) + 1 ) <= qr_pre) ” 
  &&  “ (ql_pre <= hi_pre) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ ((t_pre + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ) <= 400000) ” 
  &&  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ (ql_pre > ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (qr_pre > ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (ql_pre > lo_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ (lo_pre <= qr_pre) ” 
  &&  “ (ql_pre <= hi_pre) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (0 <= (t_pre % ( 60 ) )) ” 
  &&  “ ((t_pre % ( 60 ) ) < 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr v_pre lo_pre hi_pre ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
.

Definition query_partial_solve_wit_4 := query_partial_solve_wit_4_pure -> query_partial_solve_wit_4_aux.

Definition query_partial_solve_wit_5_pure := 
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (hi_pre > qr_pre)) (PreH4 : (ql_pre <= lo_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= hi_pre)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (1 <= ql_pre)) (PreH15 : (ql_pre <= qr_pre)) (PreH16 : (qr_pre <= n)) (PreH17 : (lo_pre <= qr_pre)) (PreH18 : (ql_pre <= hi_pre)) (PreH19 : (0 <= t_pre)) (PreH20 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH21 : (0 <= (t_pre % ( 60 ) ))) (PreH22 : ((t_pre % ( 60 ) ) < 60)) (PreH23 : (PeriodsOK arr )) (PreH24 : (CellsShaped cells )) (PreH25 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ ((((lo_pre + hi_pre ) ÷ 2 ) + 1 ) <= qr_pre) ” 
  &&  “ (ql_pre <= hi_pre) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ ((t_pre + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ) <= 400000) ” 
  &&  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
) \/
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH17 : (hi_pre > qr_pre)) (PreH18 : (ql_pre <= lo_pre)) (PreH19 : (NodeFits v_pre lo_pre hi_pre )) (PreH20 : (1 <= v_pre)) (PreH21 : (v_pre < 400020)) (PreH22 : (1 <= lo_pre)) (PreH23 : (lo_pre <= hi_pre)) (PreH24 : (hi_pre <= n)) (PreH25 : (n = (Zlength (arr)))) (PreH26 : (1 <= n)) (PreH27 : (n <= 100000)) (PreH28 : (1 <= ql_pre)) (PreH29 : (ql_pre <= qr_pre)) (PreH30 : (qr_pre <= n)) (PreH31 : (lo_pre <= qr_pre)) (PreH32 : (ql_pre <= hi_pre)) (PreH33 : (0 <= t_pre)) (PreH34 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH35 : (0 <= (t_pre % ( 60 ) ))) (PreH36 : ((t_pre % ( 60 ) ) < 60)) (PreH37 : (PeriodsOK arr )) (PreH38 : (CellsShaped cells )) (PreH39 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ ((t_pre + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ) <= 400000) ” 
  &&  “ (TreeOK cells arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
).

Definition query_partial_solve_wit_5_pure_split_goal_1 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH17 : (hi_pre > qr_pre)) (PreH18 : (ql_pre <= lo_pre)) (PreH19 : (NodeFits v_pre lo_pre hi_pre )) (PreH20 : (1 <= v_pre)) (PreH21 : (v_pre < 400020)) (PreH22 : (1 <= lo_pre)) (PreH23 : (lo_pre <= hi_pre)) (PreH24 : (hi_pre <= n)) (PreH25 : (n = (Zlength (arr)))) (PreH26 : (1 <= n)) (PreH27 : (n <= 100000)) (PreH28 : (1 <= ql_pre)) (PreH29 : (ql_pre <= qr_pre)) (PreH30 : (qr_pre <= n)) (PreH31 : (lo_pre <= qr_pre)) (PreH32 : (ql_pre <= hi_pre)) (PreH33 : (0 <= t_pre)) (PreH34 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH35 : (0 <= (t_pre % ( 60 ) ))) (PreH36 : ((t_pre % ( 60 ) ) < 60)) (PreH37 : (PeriodsOK arr )) (PreH38 : (CellsShaped cells )) (PreH39 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
.

Definition query_partial_solve_wit_5_pure_split_goal_2 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH17 : (hi_pre > qr_pre)) (PreH18 : (ql_pre <= lo_pre)) (PreH19 : (NodeFits v_pre lo_pre hi_pre )) (PreH20 : (1 <= v_pre)) (PreH21 : (v_pre < 400020)) (PreH22 : (1 <= lo_pre)) (PreH23 : (lo_pre <= hi_pre)) (PreH24 : (hi_pre <= n)) (PreH25 : (n = (Zlength (arr)))) (PreH26 : (1 <= n)) (PreH27 : (n <= 100000)) (PreH28 : (1 <= ql_pre)) (PreH29 : (ql_pre <= qr_pre)) (PreH30 : (qr_pre <= n)) (PreH31 : (lo_pre <= qr_pre)) (PreH32 : (ql_pre <= hi_pre)) (PreH33 : (0 <= t_pre)) (PreH34 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH35 : (0 <= (t_pre % ( 60 ) ))) (PreH36 : ((t_pre % ( 60 ) ) < 60)) (PreH37 : (PeriodsOK arr )) (PreH38 : (CellsShaped cells )) (PreH39 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((t_pre + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ) <= 400000) ”
.

Definition query_partial_solve_wit_5_pure_split_goal_3 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH17 : (hi_pre > qr_pre)) (PreH18 : (ql_pre <= lo_pre)) (PreH19 : (NodeFits v_pre lo_pre hi_pre )) (PreH20 : (1 <= v_pre)) (PreH21 : (v_pre < 400020)) (PreH22 : (1 <= lo_pre)) (PreH23 : (lo_pre <= hi_pre)) (PreH24 : (hi_pre <= n)) (PreH25 : (n = (Zlength (arr)))) (PreH26 : (1 <= n)) (PreH27 : (n <= 100000)) (PreH28 : (1 <= ql_pre)) (PreH29 : (ql_pre <= qr_pre)) (PreH30 : (qr_pre <= n)) (PreH31 : (lo_pre <= qr_pre)) (PreH32 : (ql_pre <= hi_pre)) (PreH33 : (0 <= t_pre)) (PreH34 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH35 : (0 <= (t_pre % ( 60 ) ))) (PreH36 : ((t_pre % ( 60 ) ) < 60)) (PreH37 : (PeriodsOK arr )) (PreH38 : (CellsShaped cells )) (PreH39 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (TreeOK cells arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
.

Definition query_partial_solve_wit_5_aux := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (hi_pre > qr_pre)) (PreH4 : (ql_pre <= lo_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= hi_pre)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (1 <= ql_pre)) (PreH15 : (ql_pre <= qr_pre)) (PreH16 : (qr_pre <= n)) (PreH17 : (lo_pre <= qr_pre)) (PreH18 : (ql_pre <= hi_pre)) (PreH19 : (0 <= t_pre)) (PreH20 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH21 : (0 <= (t_pre % ( 60 ) ))) (PreH22 : ((t_pre % ( 60 ) ) < 60)) (PreH23 : (PeriodsOK arr )) (PreH24 : (CellsShaped cells )) (PreH25 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ ((((lo_pre + hi_pre ) ÷ 2 ) + 1 ) <= qr_pre) ” 
  &&  “ (ql_pre <= hi_pre) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ ((t_pre + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ) <= 400000) ” 
  &&  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ (ql_pre > ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (qr_pre > ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (hi_pre > qr_pre) ” 
  &&  “ (ql_pre <= lo_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ (lo_pre <= qr_pre) ” 
  &&  “ (ql_pre <= hi_pre) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (0 <= (t_pre % ( 60 ) )) ” 
  &&  “ ((t_pre % ( 60 ) ) < 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr v_pre lo_pre hi_pre ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
.

Definition query_partial_solve_wit_5 := query_partial_solve_wit_5_pure -> query_partial_solve_wit_5_aux.

Definition query_partial_solve_wit_6_pure := 
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (ql_pre > lo_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= hi_pre)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (1 <= ql_pre)) (PreH14 : (ql_pre <= qr_pre)) (PreH15 : (qr_pre <= n)) (PreH16 : (lo_pre <= qr_pre)) (PreH17 : (ql_pre <= hi_pre)) (PreH18 : (0 <= t_pre)) (PreH19 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH20 : (0 <= (t_pre % ( 60 ) ))) (PreH21 : ((t_pre % ( 60 ) ) < 60)) (PreH22 : (PeriodsOK arr )) (PreH23 : (CellsShaped cells )) (PreH24 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mt" ) )) # Int  |->_)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (((lo_pre + hi_pre ) ÷ 2 ) <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ (lo_pre <= qr_pre) ” 
  &&  “ (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ ((t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ”
) \/
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH17 : (ql_pre > lo_pre)) (PreH18 : (NodeFits v_pre lo_pre hi_pre )) (PreH19 : (1 <= v_pre)) (PreH20 : (v_pre < 400020)) (PreH21 : (1 <= lo_pre)) (PreH22 : (lo_pre <= hi_pre)) (PreH23 : (hi_pre <= n)) (PreH24 : (n = (Zlength (arr)))) (PreH25 : (1 <= n)) (PreH26 : (n <= 100000)) (PreH27 : (1 <= ql_pre)) (PreH28 : (ql_pre <= qr_pre)) (PreH29 : (qr_pre <= n)) (PreH30 : (lo_pre <= qr_pre)) (PreH31 : (ql_pre <= hi_pre)) (PreH32 : (0 <= t_pre)) (PreH33 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH34 : (0 <= (t_pre % ( 60 ) ))) (PreH35 : ((t_pre % ( 60 ) ) < 60)) (PreH36 : (PeriodsOK arr )) (PreH37 : (CellsShaped cells )) (PreH38 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mt" ) )) # Int  |->_)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ ((t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (TreeOK cells arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ”
).

Definition query_partial_solve_wit_6_pure_split_goal_1 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH17 : (ql_pre > lo_pre)) (PreH18 : (NodeFits v_pre lo_pre hi_pre )) (PreH19 : (1 <= v_pre)) (PreH20 : (v_pre < 400020)) (PreH21 : (1 <= lo_pre)) (PreH22 : (lo_pre <= hi_pre)) (PreH23 : (hi_pre <= n)) (PreH24 : (n = (Zlength (arr)))) (PreH25 : (1 <= n)) (PreH26 : (n <= 100000)) (PreH27 : (1 <= ql_pre)) (PreH28 : (ql_pre <= qr_pre)) (PreH29 : (qr_pre <= n)) (PreH30 : (lo_pre <= qr_pre)) (PreH31 : (ql_pre <= hi_pre)) (PreH32 : (0 <= t_pre)) (PreH33 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH34 : (0 <= (t_pre % ( 60 ) ))) (PreH35 : ((t_pre % ( 60 ) ) < 60)) (PreH36 : (PeriodsOK arr )) (PreH37 : (CellsShaped cells )) (PreH38 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mt" ) )) # Int  |->_)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ”
.

Definition query_partial_solve_wit_6_pure_split_goal_2 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH17 : (ql_pre > lo_pre)) (PreH18 : (NodeFits v_pre lo_pre hi_pre )) (PreH19 : (1 <= v_pre)) (PreH20 : (v_pre < 400020)) (PreH21 : (1 <= lo_pre)) (PreH22 : (lo_pre <= hi_pre)) (PreH23 : (hi_pre <= n)) (PreH24 : (n = (Zlength (arr)))) (PreH25 : (1 <= n)) (PreH26 : (n <= 100000)) (PreH27 : (1 <= ql_pre)) (PreH28 : (ql_pre <= qr_pre)) (PreH29 : (qr_pre <= n)) (PreH30 : (lo_pre <= qr_pre)) (PreH31 : (ql_pre <= hi_pre)) (PreH32 : (0 <= t_pre)) (PreH33 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH34 : (0 <= (t_pre % ( 60 ) ))) (PreH35 : ((t_pre % ( 60 ) ) < 60)) (PreH36 : (PeriodsOK arr )) (PreH37 : (CellsShaped cells )) (PreH38 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mt" ) )) # Int  |->_)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ ((t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ) <= 400000) ”
.

Definition query_partial_solve_wit_6_pure_split_goal_3 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH17 : (ql_pre > lo_pre)) (PreH18 : (NodeFits v_pre lo_pre hi_pre )) (PreH19 : (1 <= v_pre)) (PreH20 : (v_pre < 400020)) (PreH21 : (1 <= lo_pre)) (PreH22 : (lo_pre <= hi_pre)) (PreH23 : (hi_pre <= n)) (PreH24 : (n = (Zlength (arr)))) (PreH25 : (1 <= n)) (PreH26 : (n <= 100000)) (PreH27 : (1 <= ql_pre)) (PreH28 : (ql_pre <= qr_pre)) (PreH29 : (qr_pre <= n)) (PreH30 : (lo_pre <= qr_pre)) (PreH31 : (ql_pre <= hi_pre)) (PreH32 : (0 <= t_pre)) (PreH33 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH34 : (0 <= (t_pre % ( 60 ) ))) (PreH35 : ((t_pre % ( 60 ) ) < 60)) (PreH36 : (PeriodsOK arr )) (PreH37 : (CellsShaped cells )) (PreH38 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mt" ) )) # Int  |->_)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (TreeOK cells arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ”
.

Definition query_partial_solve_wit_6_aux := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (ql_pre > lo_pre)) (PreH4 : (NodeFits v_pre lo_pre hi_pre )) (PreH5 : (1 <= v_pre)) (PreH6 : (v_pre < 400020)) (PreH7 : (1 <= lo_pre)) (PreH8 : (lo_pre <= hi_pre)) (PreH9 : (hi_pre <= n)) (PreH10 : (n = (Zlength (arr)))) (PreH11 : (1 <= n)) (PreH12 : (n <= 100000)) (PreH13 : (1 <= ql_pre)) (PreH14 : (ql_pre <= qr_pre)) (PreH15 : (qr_pre <= n)) (PreH16 : (lo_pre <= qr_pre)) (PreH17 : (ql_pre <= hi_pre)) (PreH18 : (0 <= t_pre)) (PreH19 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH20 : (0 <= (t_pre % ( 60 ) ))) (PreH21 : ((t_pre % ( 60 ) ) < 60)) (PreH22 : (PeriodsOK arr )) (PreH23 : (CellsShaped cells )) (PreH24 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (((lo_pre + hi_pre ) ÷ 2 ) <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ (lo_pre <= qr_pre) ” 
  &&  “ (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ ((t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (qr_pre > ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (ql_pre > lo_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ (lo_pre <= qr_pre) ” 
  &&  “ (ql_pre <= hi_pre) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (0 <= (t_pre % ( 60 ) )) ” 
  &&  “ ((t_pre % ( 60 ) ) < 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr v_pre lo_pre hi_pre ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
.

Definition query_partial_solve_wit_6 := query_partial_solve_wit_6_pure -> query_partial_solve_wit_6_aux.

Definition query_partial_solve_wit_7_pure := 
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (hi_pre > qr_pre)) (PreH4 : (ql_pre <= lo_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= hi_pre)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (1 <= ql_pre)) (PreH15 : (ql_pre <= qr_pre)) (PreH16 : (qr_pre <= n)) (PreH17 : (lo_pre <= qr_pre)) (PreH18 : (ql_pre <= hi_pre)) (PreH19 : (0 <= t_pre)) (PreH20 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH21 : (0 <= (t_pre % ( 60 ) ))) (PreH22 : ((t_pre % ( 60 ) ) < 60)) (PreH23 : (PeriodsOK arr )) (PreH24 : (CellsShaped cells )) (PreH25 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mt" ) )) # Int  |->_)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (((lo_pre + hi_pre ) ÷ 2 ) <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ (lo_pre <= qr_pre) ” 
  &&  “ (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ ((t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ”
) \/
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH17 : (hi_pre > qr_pre)) (PreH18 : (ql_pre <= lo_pre)) (PreH19 : (NodeFits v_pre lo_pre hi_pre )) (PreH20 : (1 <= v_pre)) (PreH21 : (v_pre < 400020)) (PreH22 : (1 <= lo_pre)) (PreH23 : (lo_pre <= hi_pre)) (PreH24 : (hi_pre <= n)) (PreH25 : (n = (Zlength (arr)))) (PreH26 : (1 <= n)) (PreH27 : (n <= 100000)) (PreH28 : (1 <= ql_pre)) (PreH29 : (ql_pre <= qr_pre)) (PreH30 : (qr_pre <= n)) (PreH31 : (lo_pre <= qr_pre)) (PreH32 : (ql_pre <= hi_pre)) (PreH33 : (0 <= t_pre)) (PreH34 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH35 : (0 <= (t_pre % ( 60 ) ))) (PreH36 : ((t_pre % ( 60 ) ) < 60)) (PreH37 : (PeriodsOK arr )) (PreH38 : (CellsShaped cells )) (PreH39 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mt" ) )) # Int  |->_)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ (TreeOK cells arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ”
).

Definition query_partial_solve_wit_7_pure_split_goal_1 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH17 : (hi_pre > qr_pre)) (PreH18 : (ql_pre <= lo_pre)) (PreH19 : (NodeFits v_pre lo_pre hi_pre )) (PreH20 : (1 <= v_pre)) (PreH21 : (v_pre < 400020)) (PreH22 : (1 <= lo_pre)) (PreH23 : (lo_pre <= hi_pre)) (PreH24 : (hi_pre <= n)) (PreH25 : (n = (Zlength (arr)))) (PreH26 : (1 <= n)) (PreH27 : (n <= 100000)) (PreH28 : (1 <= ql_pre)) (PreH29 : (ql_pre <= qr_pre)) (PreH30 : (qr_pre <= n)) (PreH31 : (lo_pre <= qr_pre)) (PreH32 : (ql_pre <= hi_pre)) (PreH33 : (0 <= t_pre)) (PreH34 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH35 : (0 <= (t_pre % ( 60 ) ))) (PreH36 : ((t_pre % ( 60 ) ) < 60)) (PreH37 : (PeriodsOK arr )) (PreH38 : (CellsShaped cells )) (PreH39 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mt" ) )) # Int  |->_)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ”
.

Definition query_partial_solve_wit_7_pure_split_goal_2 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (t_pre >= INT_MIN)) (PreH9 : (qr_pre >= INT_MIN)) (PreH10 : (ql_pre >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (v_pre >= INT_MIN)) (PreH14 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH15 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH16 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH17 : (hi_pre > qr_pre)) (PreH18 : (ql_pre <= lo_pre)) (PreH19 : (NodeFits v_pre lo_pre hi_pre )) (PreH20 : (1 <= v_pre)) (PreH21 : (v_pre < 400020)) (PreH22 : (1 <= lo_pre)) (PreH23 : (lo_pre <= hi_pre)) (PreH24 : (hi_pre <= n)) (PreH25 : (n = (Zlength (arr)))) (PreH26 : (1 <= n)) (PreH27 : (n <= 100000)) (PreH28 : (1 <= ql_pre)) (PreH29 : (ql_pre <= qr_pre)) (PreH30 : (qr_pre <= n)) (PreH31 : (lo_pre <= qr_pre)) (PreH32 : (ql_pre <= hi_pre)) (PreH33 : (0 <= t_pre)) (PreH34 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH35 : (0 <= (t_pre % ( 60 ) ))) (PreH36 : ((t_pre % ( 60 ) ) < 60)) (PreH37 : (PeriodsOK arr )) (PreH38 : (CellsShaped cells )) (PreH39 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  ((( &( "mt" ) )) # Int  |->_)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (TreeOK cells arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ”
.

Definition query_partial_solve_wit_7_aux := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (PreH1 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH2 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH3 : (hi_pre > qr_pre)) (PreH4 : (ql_pre <= lo_pre)) (PreH5 : (NodeFits v_pre lo_pre hi_pre )) (PreH6 : (1 <= v_pre)) (PreH7 : (v_pre < 400020)) (PreH8 : (1 <= lo_pre)) (PreH9 : (lo_pre <= hi_pre)) (PreH10 : (hi_pre <= n)) (PreH11 : (n = (Zlength (arr)))) (PreH12 : (1 <= n)) (PreH13 : (n <= 100000)) (PreH14 : (1 <= ql_pre)) (PreH15 : (ql_pre <= qr_pre)) (PreH16 : (qr_pre <= n)) (PreH17 : (lo_pre <= qr_pre)) (PreH18 : (ql_pre <= hi_pre)) (PreH19 : (0 <= t_pre)) (PreH20 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH21 : (0 <= (t_pre % ( 60 ) ))) (PreH22 : ((t_pre % ( 60 ) ) < 60)) (PreH23 : (PeriodsOK arr )) (PreH24 : (CellsShaped cells )) (PreH25 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (((lo_pre + hi_pre ) ÷ 2 ) <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ (lo_pre <= qr_pre) ” 
  &&  “ (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ ((t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ (NodeFits (2 * v_pre ) lo_pre ((lo_pre + hi_pre ) ÷ 2 ) ) ” 
  &&  “ (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (qr_pre > ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (hi_pre > qr_pre) ” 
  &&  “ (ql_pre <= lo_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ (lo_pre <= qr_pre) ” 
  &&  “ (ql_pre <= hi_pre) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (0 <= (t_pre % ( 60 ) )) ” 
  &&  “ ((t_pre % ( 60 ) ) < 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr v_pre lo_pre hi_pre ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
.

Definition query_partial_solve_wit_7 := query_partial_solve_wit_7_pure -> query_partial_solve_wit_7_aux.

Definition query_partial_solve_wit_8_pure := 
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (ql_pre > lo_pre)) (PreH7 : (NodeFits v_pre lo_pre hi_pre )) (PreH8 : (1 <= v_pre)) (PreH9 : (v_pre < 400020)) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= hi_pre)) (PreH12 : (hi_pre <= n)) (PreH13 : (n = (Zlength (arr)))) (PreH14 : (1 <= n)) (PreH15 : (n <= 100000)) (PreH16 : (1 <= ql_pre)) (PreH17 : (ql_pre <= qr_pre)) (PreH18 : (qr_pre <= n)) (PreH19 : (lo_pre <= qr_pre)) (PreH20 : (ql_pre <= hi_pre)) (PreH21 : (0 <= t_pre)) (PreH22 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH23 : (0 <= (t_pre % ( 60 ) ))) (PreH24 : ((t_pre % ( 60 ) ) < 60)) (PreH25 : (PeriodsOK arr )) (PreH26 : (CellsShaped cells )) (PreH27 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  ((( &( "mt" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ ((((lo_pre + hi_pre ) ÷ 2 ) + 1 ) <= qr_pre) ” 
  &&  “ (ql_pre <= hi_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ ((retval + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ) <= 400000) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
) \/
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (t_pre >= INT_MIN)) (PreH10 : (qr_pre >= INT_MIN)) (PreH11 : (ql_pre >= INT_MIN)) (PreH12 : (hi_pre >= INT_MIN)) (PreH13 : (lo_pre >= INT_MIN)) (PreH14 : (v_pre >= INT_MIN)) (PreH15 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH16 : (retval >= INT_MIN)) (PreH17 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH18 : (t_pre <= retval)) (PreH19 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH20 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH21 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH22 : (ql_pre > lo_pre)) (PreH23 : (NodeFits v_pre lo_pre hi_pre )) (PreH24 : (1 <= v_pre)) (PreH25 : (v_pre < 400020)) (PreH26 : (1 <= lo_pre)) (PreH27 : (lo_pre <= hi_pre)) (PreH28 : (hi_pre <= n)) (PreH29 : (n = (Zlength (arr)))) (PreH30 : (1 <= n)) (PreH31 : (n <= 100000)) (PreH32 : (1 <= ql_pre)) (PreH33 : (ql_pre <= qr_pre)) (PreH34 : (qr_pre <= n)) (PreH35 : (lo_pre <= qr_pre)) (PreH36 : (ql_pre <= hi_pre)) (PreH37 : (0 <= t_pre)) (PreH38 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH39 : (0 <= (t_pre % ( 60 ) ))) (PreH40 : ((t_pre % ( 60 ) ) < 60)) (PreH41 : (PeriodsOK arr )) (PreH42 : (CellsShaped cells )) (PreH43 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  ((( &( "mt" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ (TreeOK cells arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
).

Definition query_partial_solve_wit_8_pure_split_goal_1 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (t_pre >= INT_MIN)) (PreH10 : (qr_pre >= INT_MIN)) (PreH11 : (ql_pre >= INT_MIN)) (PreH12 : (hi_pre >= INT_MIN)) (PreH13 : (lo_pre >= INT_MIN)) (PreH14 : (v_pre >= INT_MIN)) (PreH15 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH16 : (retval >= INT_MIN)) (PreH17 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH18 : (t_pre <= retval)) (PreH19 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH20 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH21 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH22 : (ql_pre > lo_pre)) (PreH23 : (NodeFits v_pre lo_pre hi_pre )) (PreH24 : (1 <= v_pre)) (PreH25 : (v_pre < 400020)) (PreH26 : (1 <= lo_pre)) (PreH27 : (lo_pre <= hi_pre)) (PreH28 : (hi_pre <= n)) (PreH29 : (n = (Zlength (arr)))) (PreH30 : (1 <= n)) (PreH31 : (n <= 100000)) (PreH32 : (1 <= ql_pre)) (PreH33 : (ql_pre <= qr_pre)) (PreH34 : (qr_pre <= n)) (PreH35 : (lo_pre <= qr_pre)) (PreH36 : (ql_pre <= hi_pre)) (PreH37 : (0 <= t_pre)) (PreH38 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH39 : (0 <= (t_pre % ( 60 ) ))) (PreH40 : ((t_pre % ( 60 ) ) < 60)) (PreH41 : (PeriodsOK arr )) (PreH42 : (CellsShaped cells )) (PreH43 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  ((( &( "mt" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
.

Definition query_partial_solve_wit_8_pure_split_goal_2 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (t_pre >= INT_MIN)) (PreH10 : (qr_pre >= INT_MIN)) (PreH11 : (ql_pre >= INT_MIN)) (PreH12 : (hi_pre >= INT_MIN)) (PreH13 : (lo_pre >= INT_MIN)) (PreH14 : (v_pre >= INT_MIN)) (PreH15 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH16 : (retval >= INT_MIN)) (PreH17 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH18 : (t_pre <= retval)) (PreH19 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH20 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH21 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH22 : (ql_pre > lo_pre)) (PreH23 : (NodeFits v_pre lo_pre hi_pre )) (PreH24 : (1 <= v_pre)) (PreH25 : (v_pre < 400020)) (PreH26 : (1 <= lo_pre)) (PreH27 : (lo_pre <= hi_pre)) (PreH28 : (hi_pre <= n)) (PreH29 : (n = (Zlength (arr)))) (PreH30 : (1 <= n)) (PreH31 : (n <= 100000)) (PreH32 : (1 <= ql_pre)) (PreH33 : (ql_pre <= qr_pre)) (PreH34 : (qr_pre <= n)) (PreH35 : (lo_pre <= qr_pre)) (PreH36 : (ql_pre <= hi_pre)) (PreH37 : (0 <= t_pre)) (PreH38 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH39 : (0 <= (t_pre % ( 60 ) ))) (PreH40 : ((t_pre % ( 60 ) ) < 60)) (PreH41 : (PeriodsOK arr )) (PreH42 : (CellsShaped cells )) (PreH43 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  ((( &( "mt" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  “ (TreeOK cells arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
.

Definition query_partial_solve_wit_8_aux := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (ql_pre > lo_pre)) (PreH7 : (NodeFits v_pre lo_pre hi_pre )) (PreH8 : (1 <= v_pre)) (PreH9 : (v_pre < 400020)) (PreH10 : (1 <= lo_pre)) (PreH11 : (lo_pre <= hi_pre)) (PreH12 : (hi_pre <= n)) (PreH13 : (n = (Zlength (arr)))) (PreH14 : (1 <= n)) (PreH15 : (n <= 100000)) (PreH16 : (1 <= ql_pre)) (PreH17 : (ql_pre <= qr_pre)) (PreH18 : (qr_pre <= n)) (PreH19 : (lo_pre <= qr_pre)) (PreH20 : (ql_pre <= hi_pre)) (PreH21 : (0 <= t_pre)) (PreH22 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH23 : (0 <= (t_pre % ( 60 ) ))) (PreH24 : ((t_pre % ( 60 ) ) < 60)) (PreH25 : (PeriodsOK arr )) (PreH26 : (CellsShaped cells )) (PreH27 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ ((((lo_pre + hi_pre ) ÷ 2 ) + 1 ) <= qr_pre) ” 
  &&  “ (ql_pre <= hi_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ ((retval + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ) <= 400000) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre))) ” 
  &&  “ (t_pre <= retval) ” 
  &&  “ (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) )) ” 
  &&  “ (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (qr_pre > ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (ql_pre > lo_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ (lo_pre <= qr_pre) ” 
  &&  “ (ql_pre <= hi_pre) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (0 <= (t_pre % ( 60 ) )) ” 
  &&  “ ((t_pre % ( 60 ) ) < 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr v_pre lo_pre hi_pre ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
.

Definition query_partial_solve_wit_8 := query_partial_solve_wit_8_pure -> query_partial_solve_wit_8_aux.

Definition query_partial_solve_wit_9_pure := 
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (hi_pre > qr_pre)) (PreH7 : (ql_pre <= lo_pre)) (PreH8 : (NodeFits v_pre lo_pre hi_pre )) (PreH9 : (1 <= v_pre)) (PreH10 : (v_pre < 400020)) (PreH11 : (1 <= lo_pre)) (PreH12 : (lo_pre <= hi_pre)) (PreH13 : (hi_pre <= n)) (PreH14 : (n = (Zlength (arr)))) (PreH15 : (1 <= n)) (PreH16 : (n <= 100000)) (PreH17 : (1 <= ql_pre)) (PreH18 : (ql_pre <= qr_pre)) (PreH19 : (qr_pre <= n)) (PreH20 : (lo_pre <= qr_pre)) (PreH21 : (ql_pre <= hi_pre)) (PreH22 : (0 <= t_pre)) (PreH23 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH24 : (0 <= (t_pre % ( 60 ) ))) (PreH25 : ((t_pre % ( 60 ) ) < 60)) (PreH26 : (PeriodsOK arr )) (PreH27 : (CellsShaped cells )) (PreH28 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  ((( &( "mt" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ ((((lo_pre + hi_pre ) ÷ 2 ) + 1 ) <= qr_pre) ” 
  &&  “ (ql_pre <= hi_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ ((retval + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ) <= 400000) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
) \/
(
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (t_pre >= INT_MIN)) (PreH10 : (qr_pre >= INT_MIN)) (PreH11 : (ql_pre >= INT_MIN)) (PreH12 : (hi_pre >= INT_MIN)) (PreH13 : (lo_pre >= INT_MIN)) (PreH14 : (v_pre >= INT_MIN)) (PreH15 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH16 : (retval >= INT_MIN)) (PreH17 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH18 : (t_pre <= retval)) (PreH19 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH20 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH21 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH22 : (hi_pre > qr_pre)) (PreH23 : (ql_pre <= lo_pre)) (PreH24 : (NodeFits v_pre lo_pre hi_pre )) (PreH25 : (1 <= v_pre)) (PreH26 : (v_pre < 400020)) (PreH27 : (1 <= lo_pre)) (PreH28 : (lo_pre <= hi_pre)) (PreH29 : (hi_pre <= n)) (PreH30 : (n = (Zlength (arr)))) (PreH31 : (1 <= n)) (PreH32 : (n <= 100000)) (PreH33 : (1 <= ql_pre)) (PreH34 : (ql_pre <= qr_pre)) (PreH35 : (qr_pre <= n)) (PreH36 : (lo_pre <= qr_pre)) (PreH37 : (ql_pre <= hi_pre)) (PreH38 : (0 <= t_pre)) (PreH39 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH40 : (0 <= (t_pre % ( 60 ) ))) (PreH41 : ((t_pre % ( 60 ) ) < 60)) (PreH42 : (PeriodsOK arr )) (PreH43 : (CellsShaped cells )) (PreH44 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  ((( &( "mt" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ (TreeOK cells arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
).

Definition query_partial_solve_wit_9_pure_split_goal_1 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (t_pre >= INT_MIN)) (PreH10 : (qr_pre >= INT_MIN)) (PreH11 : (ql_pre >= INT_MIN)) (PreH12 : (hi_pre >= INT_MIN)) (PreH13 : (lo_pre >= INT_MIN)) (PreH14 : (v_pre >= INT_MIN)) (PreH15 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH16 : (retval >= INT_MIN)) (PreH17 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH18 : (t_pre <= retval)) (PreH19 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH20 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH21 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH22 : (hi_pre > qr_pre)) (PreH23 : (ql_pre <= lo_pre)) (PreH24 : (NodeFits v_pre lo_pre hi_pre )) (PreH25 : (1 <= v_pre)) (PreH26 : (v_pre < 400020)) (PreH27 : (1 <= lo_pre)) (PreH28 : (lo_pre <= hi_pre)) (PreH29 : (hi_pre <= n)) (PreH30 : (n = (Zlength (arr)))) (PreH31 : (1 <= n)) (PreH32 : (n <= 100000)) (PreH33 : (1 <= ql_pre)) (PreH34 : (ql_pre <= qr_pre)) (PreH35 : (qr_pre <= n)) (PreH36 : (lo_pre <= qr_pre)) (PreH37 : (ql_pre <= hi_pre)) (PreH38 : (0 <= t_pre)) (PreH39 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH40 : (0 <= (t_pre % ( 60 ) ))) (PreH41 : ((t_pre % ( 60 ) ) < 60)) (PreH42 : (PeriodsOK arr )) (PreH43 : (CellsShaped cells )) (PreH44 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  ((( &( "mt" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
.

Definition query_partial_solve_wit_9_pure_split_goal_2 := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (t_pre <= INT_MAX)) (PreH2 : (qr_pre <= INT_MAX)) (PreH3 : (ql_pre <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (((lo_pre + hi_pre ) ÷ 2 ) <= INT_MAX)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (t_pre >= INT_MIN)) (PreH10 : (qr_pre >= INT_MIN)) (PreH11 : (ql_pre >= INT_MIN)) (PreH12 : (hi_pre >= INT_MIN)) (PreH13 : (lo_pre >= INT_MIN)) (PreH14 : (v_pre >= INT_MIN)) (PreH15 : (((lo_pre + hi_pre ) ÷ 2 ) >= INT_MIN)) (PreH16 : (retval >= INT_MIN)) (PreH17 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH18 : (t_pre <= retval)) (PreH19 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH20 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH21 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH22 : (hi_pre > qr_pre)) (PreH23 : (ql_pre <= lo_pre)) (PreH24 : (NodeFits v_pre lo_pre hi_pre )) (PreH25 : (1 <= v_pre)) (PreH26 : (v_pre < 400020)) (PreH27 : (1 <= lo_pre)) (PreH28 : (lo_pre <= hi_pre)) (PreH29 : (hi_pre <= n)) (PreH30 : (n = (Zlength (arr)))) (PreH31 : (1 <= n)) (PreH32 : (n <= 100000)) (PreH33 : (1 <= ql_pre)) (PreH34 : (ql_pre <= qr_pre)) (PreH35 : (qr_pre <= n)) (PreH36 : (lo_pre <= qr_pre)) (PreH37 : (ql_pre <= hi_pre)) (PreH38 : (0 <= t_pre)) (PreH39 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH40 : (0 <= (t_pre % ( 60 ) ))) (PreH41 : ((t_pre % ( 60 ) ) < 60)) (PreH42 : (PeriodsOK arr )) (PreH43 : (CellsShaped cells )) (PreH44 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  ((( &( "mt" ) )) # Int  |-> retval)
  **  ((( &( "mid" ) )) # Int  |-> ((lo_pre + hi_pre ) ÷ 2 ))
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "ql" ) )) # Int  |-> ql_pre)
  **  ((( &( "qr" ) )) # Int  |-> qr_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
|--
  “ (TreeOK cells arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ”
.

Definition query_partial_solve_wit_9_aux := 
forall (t_pre: Z) (qr_pre: Z) (ql_pre: Z) (hi_pre: Z) (lo_pre: Z) (v_pre: Z) (n: Z) (arr: (@list Z)) (cells: (@list (@list (@option Z)))) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre)))) (PreH2 : (t_pre <= retval)) (PreH3 : (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) ))) (PreH4 : (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 ))) (PreH5 : (qr_pre > ((lo_pre + hi_pre ) ÷ 2 ))) (PreH6 : (hi_pre > qr_pre)) (PreH7 : (ql_pre <= lo_pre)) (PreH8 : (NodeFits v_pre lo_pre hi_pre )) (PreH9 : (1 <= v_pre)) (PreH10 : (v_pre < 400020)) (PreH11 : (1 <= lo_pre)) (PreH12 : (lo_pre <= hi_pre)) (PreH13 : (hi_pre <= n)) (PreH14 : (n = (Zlength (arr)))) (PreH15 : (1 <= n)) (PreH16 : (n <= 100000)) (PreH17 : (1 <= ql_pre)) (PreH18 : (ql_pre <= qr_pre)) (PreH19 : (qr_pre <= n)) (PreH20 : (lo_pre <= qr_pre)) (PreH21 : (ql_pre <= hi_pre)) (PreH22 : (0 <= t_pre)) (PreH23 : ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000)) (PreH24 : (0 <= (t_pre % ( 60 ) ))) (PreH25 : ((t_pre % ( 60 ) ) < 60)) (PreH26 : (PeriodsOK arr )) (PreH27 : (CellsShaped cells )) (PreH28 : (TreeOK cells arr v_pre lo_pre hi_pre )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ ((((lo_pre + hi_pre ) ÷ 2 ) + 1 ) <= qr_pre) ” 
  &&  “ (ql_pre <= hi_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ ((retval + (2 * ((hi_pre - (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) ) + 1 ) ) ) <= 400000) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ (NodeFits ((2 * v_pre ) + 1 ) (((lo_pre + hi_pre ) ÷ 2 ) + 1 ) hi_pre ) ” 
  &&  “ (retval = (cross ((QuerySlice (arr) (lo_pre) (((lo_pre + hi_pre ) ÷ 2 )) (ql_pre) (qr_pre))) (t_pre))) ” 
  &&  “ (t_pre <= retval) ” 
  &&  “ (retval <= (t_pre + (2 * ((((lo_pre + hi_pre ) ÷ 2 ) - lo_pre ) + 1 ) ) )) ” 
  &&  “ (ql_pre <= ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (qr_pre > ((lo_pre + hi_pre ) ÷ 2 )) ” 
  &&  “ (hi_pre > qr_pre) ” 
  &&  “ (ql_pre <= lo_pre) ” 
  &&  “ (NodeFits v_pre lo_pre hi_pre ) ” 
  &&  “ (1 <= v_pre) ” 
  &&  “ (v_pre < 400020) ” 
  &&  “ (1 <= lo_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ (hi_pre <= n) ” 
  &&  “ (n = (Zlength (arr))) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 100000) ” 
  &&  “ (1 <= ql_pre) ” 
  &&  “ (ql_pre <= qr_pre) ” 
  &&  “ (qr_pre <= n) ” 
  &&  “ (lo_pre <= qr_pre) ” 
  &&  “ (ql_pre <= hi_pre) ” 
  &&  “ (0 <= t_pre) ” 
  &&  “ ((t_pre + (2 * ((hi_pre - lo_pre ) + 1 ) ) ) <= 400000) ” 
  &&  “ (0 <= (t_pre % ( 60 ) )) ” 
  &&  “ ((t_pre % ( 60 ) ) < 60) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr v_pre lo_pre hi_pre ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
.

Definition query_partial_solve_wit_9 := query_partial_solve_wit_9_pure -> query_partial_solve_wit_9_aux.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells0 )) (PreH2 : (0 <= q_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (periods)))) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 100000)) (PreH8 : (q_pre = (Zlength (kinds)))) (PreH9 : ((Zlength (xs)) = q_pre)) (PreH10 : ((Zlength (ys)) = q_pre)) (PreH11 : ((Zlength (queries)) = q_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i periods 0)) /\ ((Znth i periods 0) <= 6)))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < q_pre)) -> ((Znth (i_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth i_2 kinds 0)) ((Znth i_2 xs 0)))) ((Znth i_2 ys 0)))))) (PreH14 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < q_pre)) -> ((((((Znth i_3 kinds 0) = 65) /\ (1 <= (Znth i_3 xs 0))) /\ ((Znth i_3 xs 0) < (Znth i_3 ys 0))) /\ ((Znth i_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth i_3 kinds 0) = 67) /\ (1 <= (Znth i_3 xs 0))) /\ ((Znth i_3 xs 0) <= n_pre)) /\ (2 <= (Znth i_3 ys 0))) /\ ((Znth i_3 ys 0) <= 6))))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
  **  (IntArray.undef_seg ( &( "a_" ) ) 1 (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_2 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0: (@list (@list (@option Z)))) (copied: (@list Z)) (i: Z) (PreH1 : (0 <= q_pre)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= q_pre)) (PreH6 : (q_pre <= 100000)) (PreH7 : ((Zlength (periods)) = n_pre)) (PreH8 : ((Zlength (kinds)) = q_pre)) (PreH9 : ((Zlength (xs)) = q_pre)) (PreH10 : ((Zlength (ys)) = q_pre)) (PreH11 : ((Zlength (queries)) = q_pre)) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH13 : (PeriodsOK periods )) (PreH14 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH15 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH16 : (1 <= i)) (PreH17 : (i <= (n_pre + 1 ))) (PreH18 : (copied = (NodeSlice (periods) (1) ((i - 1 ))))) (PreH19 : (CellsShaped cells0 )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (i + 1 ) (app (copied) ((cons ((Znth (i - 1 ) periods 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "a_" ) ) (i + 1 ) (n_pre + 1 ) )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_3 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0: (@list (@list (@option Z)))) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= q_pre)) (PreH4 : (q_pre <= 100000)) (PreH5 : ((Zlength (periods)) = n_pre)) (PreH6 : ((Zlength (kinds)) = q_pre)) (PreH7 : ((Zlength (xs)) = q_pre)) (PreH8 : ((Zlength (ys)) = q_pre)) (PreH9 : ((Zlength (queries)) = q_pre)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH11 : (PeriodsOK periods )) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH13 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH14 : (CellsShaped cells0 )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_4 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0: (@list (@list (@option Z)))) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= q_pre)) (PreH4 : (q_pre <= 100000)) (PreH5 : ((Zlength (periods)) = n_pre)) (PreH6 : ((Zlength (kinds)) = q_pre)) (PreH7 : ((Zlength (xs)) = q_pre)) (PreH8 : ((Zlength (ys)) = q_pre)) (PreH9 : ((Zlength (queries)) = q_pre)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH11 : (PeriodsOK periods )) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH13 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH14 : (CellsShaped cells0 )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 periods 1 1 n_pre )) (PreH3 : (CellsAgreeOutside 1 1 n_pre cells0 cells1 )) (PreH4 : (0 <= q_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= q_pre)) (PreH8 : (q_pre <= 100000)) (PreH9 : ((Zlength (periods)) = n_pre)) (PreH10 : ((Zlength (kinds)) = q_pre)) (PreH11 : ((Zlength (xs)) = q_pre)) (PreH12 : ((Zlength (ys)) = q_pre)) (PreH13 : ((Zlength (queries)) = q_pre)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH15 : (PeriodsOK periods )) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH17 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH18 : (CellsShaped cells0 )) ,
  ((( &( "nout" ) )) # Int  |->_)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) periods )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 periods 1 1 n_pre )) (PreH3 : (CellsAgreeOutside 1 1 n_pre cells0 cells1 )) (PreH4 : (0 <= q_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= q_pre)) (PreH8 : (q_pre <= 100000)) (PreH9 : ((Zlength (periods)) = n_pre)) (PreH10 : ((Zlength (kinds)) = q_pre)) (PreH11 : ((Zlength (xs)) = q_pre)) (PreH12 : ((Zlength (ys)) = q_pre)) (PreH13 : ((Zlength (queries)) = q_pre)) (PreH14 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH15 : (PeriodsOK periods )) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH17 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH18 : (CellsShaped cells0 )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "nout" ) )) # Int  |-> 0)
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) periods )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= q_pre)) (PreH5 : (q_pre <= 100000)) (PreH6 : ((Zlength (periods)) = n_pre)) (PreH7 : ((Zlength (kinds)) = q_pre)) (PreH8 : ((Zlength (xs)) = q_pre)) (PreH9 : ((Zlength (ys)) = q_pre)) (PreH10 : ((Zlength (queries)) = q_pre)) (PreH11 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH12 : (PeriodsOK periods )) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH14 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH15 : (0 <= i)) (PreH16 : (i <= q_pre)) (PreH17 : (0 <= nout)) (PreH18 : (nout <= i)) (PreH19 : (nout = (AskCount (queries) (i)))) (PreH20 : ((Zlength (states)) = (i + 1 ))) (PreH21 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH22 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH23 : ((Zlength (arr)) = n_pre)) (PreH24 : (PeriodsOK arr )) (PreH25 : ((Zlength (answers)) = nout)) (PreH26 : (CellsShaped cells )) (PreH27 : (TreeOK cells arr 1 1 n_pre )) (PreH28 : (QueryStepsOK queries states i )) (PreH29 : (AnswersOK queries states answers i )) ,
  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (67 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 67) ”
.

Definition solver_safety_wit_8 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (0 <= q_pre)) (PreH2 : ((Znth i kinds 0) = 67)) (PreH3 : (i < q_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 100000)) (PreH8 : ((Zlength (periods)) = n_pre)) (PreH9 : ((Zlength (kinds)) = q_pre)) (PreH10 : ((Zlength (xs)) = q_pre)) (PreH11 : ((Zlength (ys)) = q_pre)) (PreH12 : ((Zlength (queries)) = q_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH14 : (PeriodsOK periods )) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH16 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH17 : (0 <= i)) (PreH18 : (i <= q_pre)) (PreH19 : (0 <= nout)) (PreH20 : (nout <= i)) (PreH21 : (nout = (AskCount (queries) (i)))) (PreH22 : ((Zlength (states)) = (i + 1 ))) (PreH23 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH24 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH25 : ((Zlength (arr)) = n_pre)) (PreH26 : (PeriodsOK arr )) (PreH27 : ((Zlength (answers)) = nout)) (PreH28 : (CellsShaped cells )) (PreH29 : (TreeOK cells arr 1 1 n_pre )) (PreH30 : (QueryStepsOK queries states i )) (PreH31 : (AnswersOK queries states answers i )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (0 <= q_pre)) (PreH2 : ((Znth i kinds 0) = 67)) (PreH3 : (i < q_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 100000)) (PreH8 : ((Zlength (periods)) = n_pre)) (PreH9 : ((Zlength (kinds)) = q_pre)) (PreH10 : ((Zlength (xs)) = q_pre)) (PreH11 : ((Zlength (ys)) = q_pre)) (PreH12 : ((Zlength (queries)) = q_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH14 : (PeriodsOK periods )) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH16 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH17 : (0 <= i)) (PreH18 : (i <= q_pre)) (PreH19 : (0 <= nout)) (PreH20 : (nout <= i)) (PreH21 : (nout = (AskCount (queries) (i)))) (PreH22 : ((Zlength (states)) = (i + 1 ))) (PreH23 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH24 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH25 : ((Zlength (arr)) = n_pre)) (PreH26 : (PeriodsOK arr )) (PreH27 : ((Zlength (answers)) = nout)) (PreH28 : (CellsShaped cells )) (PreH29 : (TreeOK cells arr 1 1 n_pre )) (PreH30 : (QueryStepsOK queries states i )) (PreH31 : (AnswersOK queries states answers i )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (0 <= q_pre)) (PreH2 : ((Znth i kinds 0) <> 67)) (PreH3 : (i < q_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 100000)) (PreH8 : ((Zlength (periods)) = n_pre)) (PreH9 : ((Zlength (kinds)) = q_pre)) (PreH10 : ((Zlength (xs)) = q_pre)) (PreH11 : ((Zlength (ys)) = q_pre)) (PreH12 : ((Zlength (queries)) = q_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH14 : (PeriodsOK periods )) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH16 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH17 : (0 <= i)) (PreH18 : (i <= q_pre)) (PreH19 : (0 <= nout)) (PreH20 : (nout <= i)) (PreH21 : (nout = (AskCount (queries) (i)))) (PreH22 : ((Zlength (states)) = (i + 1 ))) (PreH23 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH24 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH25 : ((Zlength (arr)) = n_pre)) (PreH26 : (PeriodsOK arr )) (PreH27 : ((Zlength (answers)) = nout)) (PreH28 : (CellsShaped cells )) (PreH29 : (TreeOK cells arr 1 1 n_pre )) (PreH30 : (QueryStepsOK queries states i )) (PreH31 : (AnswersOK queries states answers i )) ,
  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (((Znth i ys 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i ys 0) - 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : ((Znth i kinds 0) <> 67)) (PreH2 : (i < q_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= q_pre)) (PreH6 : (q_pre <= 100000)) (PreH7 : ((Zlength (periods)) = n_pre)) (PreH8 : ((Zlength (kinds)) = q_pre)) (PreH9 : ((Zlength (xs)) = q_pre)) (PreH10 : ((Zlength (ys)) = q_pre)) (PreH11 : ((Zlength (queries)) = q_pre)) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH13 : (PeriodsOK periods )) (PreH14 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH15 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH16 : (0 <= i)) (PreH17 : (i <= q_pre)) (PreH18 : (0 <= nout)) (PreH19 : (nout <= i)) (PreH20 : (nout = (AskCount (queries) (i)))) (PreH21 : ((Zlength (states)) = (i + 1 ))) (PreH22 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH23 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH24 : ((Zlength (arr)) = n_pre)) (PreH25 : (PeriodsOK arr )) (PreH26 : ((Zlength (answers)) = nout)) (PreH27 : (CellsShaped cells )) (PreH28 : (TreeOK cells arr 1 1 n_pre )) (PreH29 : (QueryStepsOK queries states i )) (PreH30 : (AnswersOK queries states answers i )) ,
  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_12 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : ((Znth i kinds 0) <> 67)) (PreH2 : (i < q_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= q_pre)) (PreH6 : (q_pre <= 100000)) (PreH7 : ((Zlength (periods)) = n_pre)) (PreH8 : ((Zlength (kinds)) = q_pre)) (PreH9 : ((Zlength (xs)) = q_pre)) (PreH10 : ((Zlength (ys)) = q_pre)) (PreH11 : ((Zlength (queries)) = q_pre)) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH13 : (PeriodsOK periods )) (PreH14 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH15 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH16 : (0 <= i)) (PreH17 : (i <= q_pre)) (PreH18 : (0 <= nout)) (PreH19 : (nout <= i)) (PreH20 : (nout = (AskCount (queries) (i)))) (PreH21 : ((Zlength (states)) = (i + 1 ))) (PreH22 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH23 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH24 : ((Zlength (arr)) = n_pre)) (PreH25 : (PeriodsOK arr )) (PreH26 : ((Zlength (answers)) = nout)) (PreH27 : (CellsShaped cells )) (PreH28 : (TreeOK cells arr 1 1 n_pre )) (PreH29 : (QueryStepsOK queries states i )) (PreH30 : (AnswersOK queries states answers i )) ,
  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_13 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (0 <= q_pre)) (PreH2 : ((Znth i kinds 0) <> 67)) (PreH3 : (i < q_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 100000)) (PreH8 : ((Zlength (periods)) = n_pre)) (PreH9 : ((Zlength (kinds)) = q_pre)) (PreH10 : ((Zlength (xs)) = q_pre)) (PreH11 : ((Zlength (ys)) = q_pre)) (PreH12 : ((Zlength (queries)) = q_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH14 : (PeriodsOK periods )) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH16 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH17 : (0 <= i)) (PreH18 : (i <= q_pre)) (PreH19 : (0 <= nout)) (PreH20 : (nout <= i)) (PreH21 : (nout = (AskCount (queries) (i)))) (PreH22 : ((Zlength (states)) = (i + 1 ))) (PreH23 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH24 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH25 : ((Zlength (arr)) = n_pre)) (PreH26 : (PeriodsOK arr )) (PreH27 : ((Zlength (answers)) = nout)) (PreH28 : (CellsShaped cells )) (PreH29 : (TreeOK cells arr 1 1 n_pre )) (PreH30 : (QueryStepsOK queries states i )) (PreH31 : (AnswersOK queries states answers i )) ,
  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_14 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (0 <= q_pre)) (PreH2 : ((Znth i kinds 0) <> 67)) (PreH3 : (i < q_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 100000)) (PreH8 : ((Zlength (periods)) = n_pre)) (PreH9 : ((Zlength (kinds)) = q_pre)) (PreH10 : ((Zlength (xs)) = q_pre)) (PreH11 : ((Zlength (ys)) = q_pre)) (PreH12 : ((Zlength (queries)) = q_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH14 : (PeriodsOK periods )) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH16 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH17 : (0 <= i)) (PreH18 : (i <= q_pre)) (PreH19 : (0 <= nout)) (PreH20 : (nout <= i)) (PreH21 : (nout = (AskCount (queries) (i)))) (PreH22 : ((Zlength (states)) = (i + 1 ))) (PreH23 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH24 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH25 : ((Zlength (arr)) = n_pre)) (PreH26 : (PeriodsOK arr )) (PreH27 : ((Zlength (answers)) = nout)) (PreH28 : (CellsShaped cells )) (PreH29 : (TreeOK cells arr 1 1 n_pre )) (PreH30 : (QueryStepsOK queries states i )) (PreH31 : (AnswersOK queries states answers i )) ,
  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_15 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (1) (n_pre) ((Znth i xs 0)) (((Znth i ys 0) - 1 )))) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= (0 + (2 * ((n_pre - 1 ) + 1 ) ) ))) (PreH4 : (0 <= q_pre)) (PreH5 : ((Znth i kinds 0) <> 67)) (PreH6 : (i < q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 100000)) (PreH11 : ((Zlength (periods)) = n_pre)) (PreH12 : ((Zlength (kinds)) = q_pre)) (PreH13 : ((Zlength (xs)) = q_pre)) (PreH14 : ((Zlength (ys)) = q_pre)) (PreH15 : ((Zlength (queries)) = q_pre)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH17 : (PeriodsOK periods )) (PreH18 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH19 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH20 : (0 <= i)) (PreH21 : (i <= q_pre)) (PreH22 : (0 <= nout)) (PreH23 : (nout <= i)) (PreH24 : (nout = (AskCount (queries) (i)))) (PreH25 : ((Zlength (states)) = (i + 1 ))) (PreH26 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH27 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH28 : ((Zlength (arr)) = n_pre)) (PreH29 : (PeriodsOK arr )) (PreH30 : ((Zlength (answers)) = nout)) (PreH31 : (CellsShaped cells )) (PreH32 : (TreeOK cells arr 1 1 n_pre )) (PreH33 : (QueryStepsOK queries states i )) (PreH34 : (AnswersOK queries states answers i )) ,
  (IntArray.full out_pre (nout + 1 ) (app (answers) ((cons (retval) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (nout + 1 ) q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
|--
  “ ((nout + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nout + 1 )) ”
.

Definition solver_safety_wit_16 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (1) (n_pre) ((Znth i xs 0)) (((Znth i ys 0) - 1 )))) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= (0 + (2 * ((n_pre - 1 ) + 1 ) ) ))) (PreH4 : (0 <= q_pre)) (PreH5 : ((Znth i kinds 0) <> 67)) (PreH6 : (i < q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 100000)) (PreH11 : ((Zlength (periods)) = n_pre)) (PreH12 : ((Zlength (kinds)) = q_pre)) (PreH13 : ((Zlength (xs)) = q_pre)) (PreH14 : ((Zlength (ys)) = q_pre)) (PreH15 : ((Zlength (queries)) = q_pre)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH17 : (PeriodsOK periods )) (PreH18 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH19 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH20 : (0 <= i)) (PreH21 : (i <= q_pre)) (PreH22 : (0 <= nout)) (PreH23 : (nout <= i)) (PreH24 : (nout = (AskCount (queries) (i)))) (PreH25 : ((Zlength (states)) = (i + 1 ))) (PreH26 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH27 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH28 : ((Zlength (arr)) = n_pre)) (PreH29 : (PeriodsOK arr )) (PreH30 : ((Zlength (answers)) = nout)) (PreH31 : (CellsShaped cells )) (PreH32 : (TreeOK cells arr 1 1 n_pre )) (PreH33 : (QueryStepsOK queries states i )) (PreH34 : (AnswersOK queries states answers i )) ,
  (IntArray.full out_pre (nout + 1 ) (app (answers) ((cons (retval) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (nout + 1 ) q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_17 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) 1 1 n_pre )) (PreH3 : (CellsAgreeOutside 1 1 n_pre cells cells1 )) (PreH4 : (0 <= q_pre)) (PreH5 : ((Znth i kinds 0) = 67)) (PreH6 : (i < q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 100000)) (PreH11 : ((Zlength (periods)) = n_pre)) (PreH12 : ((Zlength (kinds)) = q_pre)) (PreH13 : ((Zlength (xs)) = q_pre)) (PreH14 : ((Zlength (ys)) = q_pre)) (PreH15 : ((Zlength (queries)) = q_pre)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH17 : (PeriodsOK periods )) (PreH18 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH19 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH20 : (0 <= i)) (PreH21 : (i <= q_pre)) (PreH22 : (0 <= nout)) (PreH23 : (nout <= i)) (PreH24 : (nout = (AskCount (queries) (i)))) (PreH25 : ((Zlength (states)) = (i + 1 ))) (PreH26 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH27 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH28 : ((Zlength (arr)) = n_pre)) (PreH29 : (PeriodsOK arr )) (PreH30 : ((Zlength (answers)) = nout)) (PreH31 : (CellsShaped cells )) (PreH32 : (TreeOK cells arr 1 1 n_pre )) (PreH33 : (QueryStepsOK queries states i )) (PreH34 : (AnswersOK queries states answers i )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_18 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (1) (n_pre) ((Znth i xs 0)) (((Znth i ys 0) - 1 )))) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= (0 + (2 * ((n_pre - 1 ) + 1 ) ) ))) (PreH4 : (0 <= q_pre)) (PreH5 : ((Znth i kinds 0) <> 67)) (PreH6 : (i < q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 100000)) (PreH11 : ((Zlength (periods)) = n_pre)) (PreH12 : ((Zlength (kinds)) = q_pre)) (PreH13 : ((Zlength (xs)) = q_pre)) (PreH14 : ((Zlength (ys)) = q_pre)) (PreH15 : ((Zlength (queries)) = q_pre)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH17 : (PeriodsOK periods )) (PreH18 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH19 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH20 : (0 <= i)) (PreH21 : (i <= q_pre)) (PreH22 : (0 <= nout)) (PreH23 : (nout <= i)) (PreH24 : (nout = (AskCount (queries) (i)))) (PreH25 : ((Zlength (states)) = (i + 1 ))) (PreH26 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH27 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH28 : ((Zlength (arr)) = n_pre)) (PreH29 : (PeriodsOK arr )) (PreH30 : ((Zlength (answers)) = nout)) (PreH31 : (CellsShaped cells )) (PreH32 : (TreeOK cells arr 1 1 n_pre )) (PreH33 : (QueryStepsOK queries states i )) (PreH34 : (AnswersOK queries states answers i )) ,
  (IntArray.full out_pre (nout + 1 ) (app (answers) ((cons (retval) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (nout + 1 ) q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> (nout + 1 ))
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0_2: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells0_2 )) (PreH2 : (0 <= q_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (periods)))) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 100000)) (PreH8 : (q_pre = (Zlength (kinds)))) (PreH9 : ((Zlength (xs)) = q_pre)) (PreH10 : ((Zlength (ys)) = q_pre)) (PreH11 : ((Zlength (queries)) = q_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i periods 0)) /\ ((Znth i periods 0) <= 6)))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < q_pre)) -> ((Znth (i_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth i_2 kinds 0)) ((Znth i_2 xs 0)))) ((Znth i_2 ys 0)))))) (PreH14 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < q_pre)) -> ((((((Znth i_3 kinds 0) = 65) /\ (1 <= (Znth i_3 xs 0))) /\ ((Znth i_3 xs 0) < (Znth i_3 ys 0))) /\ ((Znth i_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth i_3 kinds 0) = 67) /\ (1 <= (Znth i_3 xs 0))) /\ ((Znth i_3 xs 0) <= n_pre)) /\ (2 <= (Znth i_3 ys 0))) /\ ((Znth i_3 ys 0) <= 6))))) ,
  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0_2 )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
  **  (IntArray.undef_seg ( &( "a_" ) ) 1 (n_pre + 1 ) )
|--
  EX (cells0: (@list (@list (@option Z))))  (copied: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ ((Zlength (kinds)) = q_pre) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6))) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0))))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6)))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (copied = (NodeSlice (periods) (1) ((1 - 1 )))) ” 
  &&  “ (CellsShaped cells0 ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.seg ( &( "a_" ) ) 1 1 copied )
  **  (IntArray.undef_seg ( &( "a_" ) ) 1 (n_pre + 1 ) )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0 )
) \/
(
forall (q_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0_2: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells0_2 )) (PreH2 : (0 <= q_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (periods)))) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 100000)) (PreH8 : (q_pre = (Zlength (kinds)))) (PreH9 : ((Zlength (xs)) = q_pre)) (PreH10 : ((Zlength (ys)) = q_pre)) (PreH11 : ((Zlength (queries)) = q_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i periods 0)) /\ ((Znth i periods 0) <= 6)))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < q_pre)) -> ((Znth (i_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth i_2 kinds 0)) ((Znth i_2 xs 0)))) ((Znth i_2 ys 0)))))) (PreH14 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < q_pre)) -> ((((((Znth i_3 kinds 0) = 65) /\ (1 <= (Znth i_3 xs 0))) /\ ((Znth i_3 xs 0) < (Znth i_3 ys 0))) /\ ((Znth i_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth i_3 kinds 0) = 67) /\ (1 <= (Znth i_3 xs 0))) /\ ((Znth i_3 xs 0) <= n_pre)) /\ (2 <= (Znth i_3 ys 0))) /\ ((Znth i_3 ys 0) <= 6))))) ,
  TT && emp 
|--
  “ ((@nil Z) = (NodeSlice (periods) (1) ((1 - 1 )))) ” 
  &&  “ (PeriodsOK periods ) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (q_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0_2: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells0_2 )) (PreH2 : (0 <= q_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (periods)))) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 100000)) (PreH8 : (q_pre = (Zlength (kinds)))) (PreH9 : ((Zlength (xs)) = q_pre)) (PreH10 : ((Zlength (ys)) = q_pre)) (PreH11 : ((Zlength (queries)) = q_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i periods 0)) /\ ((Znth i periods 0) <= 6)))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < q_pre)) -> ((Znth (i_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth i_2 kinds 0)) ((Znth i_2 xs 0)))) ((Znth i_2 ys 0)))))) (PreH14 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < q_pre)) -> ((((((Znth i_3 kinds 0) = 65) /\ (1 <= (Znth i_3 xs 0))) /\ ((Znth i_3 xs 0) < (Znth i_3 ys 0))) /\ ((Znth i_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth i_3 kinds 0) = 67) /\ (1 <= (Znth i_3 xs 0))) /\ ((Znth i_3 xs 0) <= n_pre)) /\ (2 <= (Znth i_3 ys 0))) /\ ((Znth i_3 ys 0) <= 6))))) ,
  ((@nil Z) = (NodeSlice (periods) (1) ((1 - 1 ))))
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (q_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0_2: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells0_2 )) (PreH2 : (0 <= q_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (periods)))) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 100000)) (PreH8 : (q_pre = (Zlength (kinds)))) (PreH9 : ((Zlength (xs)) = q_pre)) (PreH10 : ((Zlength (ys)) = q_pre)) (PreH11 : ((Zlength (queries)) = q_pre)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i periods 0)) /\ ((Znth i periods 0) <= 6)))) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < q_pre)) -> ((Znth (i_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth i_2 kinds 0)) ((Znth i_2 xs 0)))) ((Znth i_2 ys 0)))))) (PreH14 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < q_pre)) -> ((((((Znth i_3 kinds 0) = 65) /\ (1 <= (Znth i_3 xs 0))) /\ ((Znth i_3 xs 0) < (Znth i_3 ys 0))) /\ ((Znth i_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth i_3 kinds 0) = 67) /\ (1 <= (Znth i_3 xs 0))) /\ ((Znth i_3 xs 0) <= n_pre)) /\ (2 <= (Znth i_3 ys 0))) /\ ((Znth i_3 ys 0) <= 6))))) ,
  (PeriodsOK periods )
.

Definition solver_entail_wit_2 := 
(
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0_2: (@list (@list (@option Z)))) (copied_2: (@list Z)) (i: Z) (PreH1 : (0 <= q_pre)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= q_pre)) (PreH6 : (q_pre <= 100000)) (PreH7 : ((Zlength (periods)) = n_pre)) (PreH8 : ((Zlength (kinds)) = q_pre)) (PreH9 : ((Zlength (xs)) = q_pre)) (PreH10 : ((Zlength (ys)) = q_pre)) (PreH11 : ((Zlength (queries)) = q_pre)) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH13 : (PeriodsOK periods )) (PreH14 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH15 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH16 : (1 <= i)) (PreH17 : (i <= (n_pre + 1 ))) (PreH18 : (copied_2 = (NodeSlice (periods) (1) ((i - 1 ))))) (PreH19 : (CellsShaped cells0_2 )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (i + 1 ) (app (copied_2) ((cons ((Znth (i - 1 ) periods 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "a_" ) ) (i + 1 ) (n_pre + 1 ) )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0_2 )
|--
  EX (cells0: (@list (@list (@option Z))))  (copied: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ ((Zlength (kinds)) = q_pre) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6))) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0))))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6)))) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (copied = (NodeSlice (periods) (1) (((i + 1 ) - 1 )))) ” 
  &&  “ (CellsShaped cells0 ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.seg ( &( "a_" ) ) 1 (i + 1 ) copied )
  **  (IntArray.undef_seg ( &( "a_" ) ) (i + 1 ) (n_pre + 1 ) )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0 )
) \/
(
forall (q_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0_2: (@list (@list (@option Z)))) (copied_2: (@list Z)) (i: Z) (PreH1 : (0 <= q_pre)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= q_pre)) (PreH6 : (q_pre <= 100000)) (PreH7 : ((Zlength (periods)) = n_pre)) (PreH8 : ((Zlength (kinds)) = q_pre)) (PreH9 : ((Zlength (xs)) = q_pre)) (PreH10 : ((Zlength (ys)) = q_pre)) (PreH11 : ((Zlength (queries)) = q_pre)) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH13 : (PeriodsOK periods )) (PreH14 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH15 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH16 : (1 <= i)) (PreH17 : (i <= (n_pre + 1 ))) (PreH18 : (copied_2 = (NodeSlice (periods) (1) ((i - 1 ))))) (PreH19 : (CellsShaped cells0_2 )) ,
  TT && emp 
|--
  “ ((app (copied_2) ((cons ((Znth (i - 1 ) periods 0)) ((@nil Z))))) = (NodeSlice (periods) (1) (((i + 1 ) - 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (q_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0_2: (@list (@list (@option Z)))) (copied_2: (@list Z)) (i: Z) (PreH1 : (0 <= q_pre)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= q_pre)) (PreH6 : (q_pre <= 100000)) (PreH7 : ((Zlength (periods)) = n_pre)) (PreH8 : ((Zlength (kinds)) = q_pre)) (PreH9 : ((Zlength (xs)) = q_pre)) (PreH10 : ((Zlength (ys)) = q_pre)) (PreH11 : ((Zlength (queries)) = q_pre)) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH13 : (PeriodsOK periods )) (PreH14 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH15 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH16 : (1 <= i)) (PreH17 : (i <= (n_pre + 1 ))) (PreH18 : (copied_2 = (NodeSlice (periods) (1) ((i - 1 ))))) (PreH19 : (CellsShaped cells0_2 )) ,
  ((app (copied_2) ((cons ((Znth (i - 1 ) periods 0)) ((@nil Z))))) = (NodeSlice (periods) (1) (((i + 1 ) - 1 ))))
.

Definition solver_entail_wit_3 := 
(
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0_2: (@list (@list (@option Z)))) (copied: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= q_pre)) (PreH5 : (q_pre <= 100000)) (PreH6 : ((Zlength (periods)) = n_pre)) (PreH7 : ((Zlength (kinds)) = q_pre)) (PreH8 : ((Zlength (xs)) = q_pre)) (PreH9 : ((Zlength (ys)) = q_pre)) (PreH10 : ((Zlength (queries)) = q_pre)) (PreH11 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> ((2 <= (Znth j_4 periods 0)) /\ ((Znth j_4 periods 0) <= 6)))) (PreH12 : (PeriodsOK periods )) (PreH13 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < q_pre)) -> ((Znth (j_5) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_5 kinds 0)) ((Znth j_5 xs 0)))) ((Znth j_5 ys 0)))))) (PreH14 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < q_pre)) -> ((((((Znth j_6 kinds 0) = 65) /\ (1 <= (Znth j_6 xs 0))) /\ ((Znth j_6 xs 0) < (Znth j_6 ys 0))) /\ ((Znth j_6 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_6 kinds 0) = 67) /\ (1 <= (Znth j_6 xs 0))) /\ ((Znth j_6 xs 0) <= n_pre)) /\ (2 <= (Znth j_6 ys 0))) /\ ((Znth j_6 ys 0) <= 6))))) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (copied = (NodeSlice (periods) (1) ((i - 1 ))))) (PreH18 : (CellsShaped cells0_2 )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.seg ( &( "a_" ) ) 1 i copied )
  **  (IntArray.undef_seg ( &( "a_" ) ) i (n_pre + 1 ) )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0_2 )
|--
  EX (cells0: (@list (@list (@option Z)))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ ((Zlength (kinds)) = q_pre) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6))) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0))))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6)))) ” 
  &&  “ (CellsShaped cells0 ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0 )
) \/
(
forall (q_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0_2: (@list (@list (@option Z)))) (copied: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= q_pre)) (PreH5 : (q_pre <= 100000)) (PreH6 : ((Zlength (periods)) = n_pre)) (PreH7 : ((Zlength (kinds)) = q_pre)) (PreH8 : ((Zlength (xs)) = q_pre)) (PreH9 : ((Zlength (ys)) = q_pre)) (PreH10 : ((Zlength (queries)) = q_pre)) (PreH11 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> ((2 <= (Znth j_4 periods 0)) /\ ((Znth j_4 periods 0) <= 6)))) (PreH12 : (PeriodsOK periods )) (PreH13 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < q_pre)) -> ((Znth (j_5) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_5 kinds 0)) ((Znth j_5 xs 0)))) ((Znth j_5 ys 0)))))) (PreH14 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < q_pre)) -> ((((((Znth j_6 kinds 0) = 65) /\ (1 <= (Znth j_6 xs 0))) /\ ((Znth j_6 xs 0) < (Znth j_6 ys 0))) /\ ((Znth j_6 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_6 kinds 0) = 67) /\ (1 <= (Znth j_6 xs 0))) /\ ((Znth j_6 xs 0) <= n_pre)) /\ (2 <= (Znth j_6 ys 0))) /\ ((Znth j_6 ys 0) <= 6))))) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (copied = (NodeSlice (periods) (1) ((i - 1 ))))) (PreH18 : (CellsShaped cells0_2 )) ,
  (IntArray.seg ( &( "a_" ) ) 1 i copied )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0_2 )
|--
  EX (cells0: (@list (@list (@option Z)))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ ((Zlength (kinds)) = q_pre) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6))) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0))))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6)))) ” 
  &&  “ (CellsShaped cells0 ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) periods )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0 )
).

Definition solver_entail_wit_4 := 
(
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 periods 1 1 n_pre )) (PreH3 : (CellsAgreeOutside 1 1 n_pre cells0 cells1 )) (PreH4 : (0 <= q_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= q_pre)) (PreH8 : (q_pre <= 100000)) (PreH9 : ((Zlength (periods)) = n_pre)) (PreH10 : ((Zlength (kinds)) = q_pre)) (PreH11 : ((Zlength (xs)) = q_pre)) (PreH12 : ((Zlength (ys)) = q_pre)) (PreH13 : ((Zlength (queries)) = q_pre)) (PreH14 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> ((2 <= (Znth j_4 periods 0)) /\ ((Znth j_4 periods 0) <= 6)))) (PreH15 : (PeriodsOK periods )) (PreH16 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < q_pre)) -> ((Znth (j_5) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_5 kinds 0)) ((Znth j_5 xs 0)))) ((Znth j_5 ys 0)))))) (PreH17 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < q_pre)) -> ((((((Znth j_6 kinds 0) = 65) /\ (1 <= (Znth j_6 xs 0))) /\ ((Znth j_6 xs 0) < (Znth j_6 ys 0))) /\ ((Znth j_6 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_6 kinds 0) = 67) /\ (1 <= (Znth j_6 xs 0))) /\ ((Znth j_6 xs 0) <= n_pre)) /\ (2 <= (Znth j_6 ys 0))) /\ ((Znth j_6 ys 0) <= 6))))) (PreH18 : (CellsShaped cells0 )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) periods )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
|--
  EX (cells: (@list (@list (@option Z))))  (answers: (@list Z))  (arr: (@list Z))  (states: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ ((Zlength (kinds)) = q_pre) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6))) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0))))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6)))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (AskCount (queries) (0))) ” 
  &&  “ ((Zlength (states)) = (0 + 1 )) ” 
  &&  “ ((Znth (0) (states) ((@nil Z))) = periods) ” 
  &&  “ (arr = (Znth (0) (states) ((@nil Z)))) ” 
  &&  “ ((Zlength (arr)) = n_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ ((Zlength (answers)) = 0) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr 1 1 n_pre ) ” 
  &&  “ (QueryStepsOK queries states 0 ) ” 
  &&  “ (AnswersOK queries states answers 0 ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full out_pre 0 answers )
  **  (IntArray.undef_seg out_pre 0 q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
) \/
(
forall (q_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0: (@list (@list (@option Z)))) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 periods 1 1 n_pre )) (PreH3 : (CellsAgreeOutside 1 1 n_pre cells0 cells1 )) (PreH4 : (0 <= q_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= q_pre)) (PreH8 : (q_pre <= 100000)) (PreH9 : ((Zlength (periods)) = n_pre)) (PreH10 : ((Zlength (kinds)) = q_pre)) (PreH11 : ((Zlength (xs)) = q_pre)) (PreH12 : ((Zlength (ys)) = q_pre)) (PreH13 : ((Zlength (queries)) = q_pre)) (PreH14 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < n_pre)) -> ((2 <= (Znth j_4 periods 0)) /\ ((Znth j_4 periods 0) <= 6)))) (PreH15 : (PeriodsOK periods )) (PreH16 : forall (j_5: Z) , (((0 <= j_5) /\ (j_5 < q_pre)) -> ((Znth (j_5) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_5 kinds 0)) ((Znth j_5 xs 0)))) ((Znth j_5 ys 0)))))) (PreH17 : forall (j_6: Z) , (((0 <= j_6) /\ (j_6 < q_pre)) -> ((((((Znth j_6 kinds 0) = 65) /\ (1 <= (Znth j_6 xs 0))) /\ ((Znth j_6 xs 0) < (Znth j_6 ys 0))) /\ ((Znth j_6 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_6 kinds 0) = 67) /\ (1 <= (Znth j_6 xs 0))) /\ ((Znth j_6 xs 0) <= n_pre)) /\ (2 <= (Znth j_6 ys 0))) /\ ((Znth j_6 ys 0) <= 6))))) (PreH18 : (CellsShaped cells0 )) ,
  TT && emp 
|--
  EX (states: (@list (@list Z))) ,
  “ (periods = (Znth (0) (states) ((@nil Z)))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (AskCount (queries) (0))) ” 
  &&  “ ((Zlength (states)) = (0 + 1 )) ” 
  &&  “ ((Znth (0) (states) ((@nil Z))) = periods) ” 
  &&  “ ((Zlength ((Znth (0) (states) ((@nil Z))))) = (Zlength (periods))) ” 
  &&  “ (PeriodsOK (Znth (0) (states) ((@nil Z))) ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ (TreeOK cells1 (Znth (0) (states) ((@nil Z))) 1 1 (Zlength (periods)) ) ” 
  &&  “ (QueryStepsOK queries states 0 ) ” 
  &&  “ (AnswersOK queries states (@nil Z) 0 ) ”
  &&  emp
).

Definition solver_entail_wit_5_1 := 
(
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells_2: (@list (@list (@option Z)))) (answers_2: (@list Z)) (arr_2: (@list Z)) (states_2: (@list (@list Z))) (nout: Z) (i: Z) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr_2)) 1 1 n_pre )) (PreH3 : (CellsAgreeOutside 1 1 n_pre cells_2 cells1 )) (PreH4 : (0 <= q_pre)) (PreH5 : ((Znth i kinds 0) = 67)) (PreH6 : (i < q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 100000)) (PreH11 : ((Zlength (periods)) = n_pre)) (PreH12 : ((Zlength (kinds)) = q_pre)) (PreH13 : ((Zlength (xs)) = q_pre)) (PreH14 : ((Zlength (ys)) = q_pre)) (PreH15 : ((Zlength (queries)) = q_pre)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH17 : (PeriodsOK periods )) (PreH18 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH19 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH20 : (0 <= i)) (PreH21 : (i <= q_pre)) (PreH22 : (0 <= nout)) (PreH23 : (nout <= i)) (PreH24 : (nout = (AskCount (queries) (i)))) (PreH25 : ((Zlength (states_2)) = (i + 1 ))) (PreH26 : ((Znth (0) (states_2) ((@nil Z))) = periods)) (PreH27 : (arr_2 = (Znth (i) (states_2) ((@nil Z))))) (PreH28 : ((Zlength (arr_2)) = n_pre)) (PreH29 : (PeriodsOK arr_2 )) (PreH30 : ((Zlength (answers_2)) = nout)) (PreH31 : (CellsShaped cells_2 )) (PreH32 : (TreeOK cells_2 arr_2 1 1 n_pre )) (PreH33 : (QueryStepsOK queries states_2 i )) (PreH34 : (AnswersOK queries states_2 answers_2 i )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr_2)) )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells1 )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers_2 )
  **  (IntArray.undef_seg out_pre nout q_pre )
|--
  EX (cells: (@list (@list (@option Z))))  (answers: (@list Z))  (arr: (@list Z))  (states: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ ((Zlength (kinds)) = q_pre) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6))) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0))))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6)))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= q_pre) ” 
  &&  “ (0 <= nout) ” 
  &&  “ (nout <= (i + 1 )) ” 
  &&  “ (nout = (AskCount (queries) ((i + 1 )))) ” 
  &&  “ ((Zlength (states)) = ((i + 1 ) + 1 )) ” 
  &&  “ ((Znth (0) (states) ((@nil Z))) = periods) ” 
  &&  “ (arr = (Znth ((i + 1 )) (states) ((@nil Z)))) ” 
  &&  “ ((Zlength (arr)) = n_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ ((Zlength (answers)) = nout) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr 1 1 n_pre ) ” 
  &&  “ (QueryStepsOK queries states (i + 1 ) ) ” 
  &&  “ (AnswersOK queries states answers (i + 1 ) ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
) \/
(
forall (q_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells_2: (@list (@list (@option Z)))) (answers_2: (@list Z)) (arr_2: (@list Z)) (states_2: (@list (@list Z))) (nout: Z) (i: Z) (cells1: (@list (@list (@option Z)))) (PreH1 : (CellsShaped cells1 )) (PreH2 : (TreeOK cells1 (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr_2)) 1 1 n_pre )) (PreH3 : (CellsAgreeOutside 1 1 n_pre cells_2 cells1 )) (PreH4 : (0 <= q_pre)) (PreH5 : ((Znth i kinds 0) = 67)) (PreH6 : (i < q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 100000)) (PreH11 : ((Zlength (periods)) = n_pre)) (PreH12 : ((Zlength (kinds)) = q_pre)) (PreH13 : ((Zlength (xs)) = q_pre)) (PreH14 : ((Zlength (ys)) = q_pre)) (PreH15 : ((Zlength (queries)) = q_pre)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH17 : (PeriodsOK periods )) (PreH18 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH19 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH20 : (0 <= i)) (PreH21 : (i <= q_pre)) (PreH22 : (0 <= nout)) (PreH23 : (nout <= i)) (PreH24 : (nout = (AskCount (queries) (i)))) (PreH25 : ((Zlength (states_2)) = (i + 1 ))) (PreH26 : ((Znth (0) (states_2) ((@nil Z))) = periods)) (PreH27 : (arr_2 = (Znth (i) (states_2) ((@nil Z))))) (PreH28 : ((Zlength (arr_2)) = n_pre)) (PreH29 : (PeriodsOK arr_2 )) (PreH30 : ((Zlength (answers_2)) = nout)) (PreH31 : (CellsShaped cells_2 )) (PreH32 : (TreeOK cells_2 arr_2 1 1 n_pre )) (PreH33 : (QueryStepsOK queries states_2 i )) (PreH34 : (AnswersOK queries states_2 answers_2 i )) ,
  TT && emp 
|--
  EX (states: (@list (@list Z))) ,
  “ ((replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) ((Znth (i) (states_2) ((@nil Z))))) = (Znth ((i + 1 )) (states) ((@nil Z)))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (kinds))) ” 
  &&  “ ((AskCount (queries) (i)) <= (i + 1 )) ” 
  &&  “ ((AskCount (queries) (i)) = (AskCount (queries) ((i + 1 )))) ” 
  &&  “ ((Zlength (states)) = ((i + 1 ) + 1 )) ” 
  &&  “ ((Znth (0) (states) ((@nil Z))) = (Znth (0) (states_2) ((@nil Z)))) ” 
  &&  “ ((Zlength ((Znth ((i + 1 )) (states) ((@nil Z))))) = (Zlength ((Znth (0) (states_2) ((@nil Z)))))) ” 
  &&  “ (PeriodsOK (Znth ((i + 1 )) (states) ((@nil Z))) ) ” 
  &&  “ (TreeOK cells1 (Znth ((i + 1 )) (states) ((@nil Z))) 1 1 (Zlength ((Znth (0) (states_2) ((@nil Z))))) ) ” 
  &&  “ (QueryStepsOK queries states (i + 1 ) ) ” 
  &&  “ (AnswersOK queries states answers_2 (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_5_2 := 
(
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells_2: (@list (@list (@option Z)))) (answers_2: (@list Z)) (arr_2: (@list Z)) (states_2: (@list (@list Z))) (nout: Z) (i: Z) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr_2) (1) (n_pre) ((Znth i xs 0)) (((Znth i ys 0) - 1 )))) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= (0 + (2 * ((n_pre - 1 ) + 1 ) ) ))) (PreH4 : (0 <= q_pre)) (PreH5 : ((Znth i kinds 0) <> 67)) (PreH6 : (i < q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 100000)) (PreH11 : ((Zlength (periods)) = n_pre)) (PreH12 : ((Zlength (kinds)) = q_pre)) (PreH13 : ((Zlength (xs)) = q_pre)) (PreH14 : ((Zlength (ys)) = q_pre)) (PreH15 : ((Zlength (queries)) = q_pre)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH17 : (PeriodsOK periods )) (PreH18 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH19 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH20 : (0 <= i)) (PreH21 : (i <= q_pre)) (PreH22 : (0 <= nout)) (PreH23 : (nout <= i)) (PreH24 : (nout = (AskCount (queries) (i)))) (PreH25 : ((Zlength (states_2)) = (i + 1 ))) (PreH26 : ((Znth (0) (states_2) ((@nil Z))) = periods)) (PreH27 : (arr_2 = (Znth (i) (states_2) ((@nil Z))))) (PreH28 : ((Zlength (arr_2)) = n_pre)) (PreH29 : (PeriodsOK arr_2 )) (PreH30 : ((Zlength (answers_2)) = nout)) (PreH31 : (CellsShaped cells_2 )) (PreH32 : (TreeOK cells_2 arr_2 1 1 n_pre )) (PreH33 : (QueryStepsOK queries states_2 i )) (PreH34 : (AnswersOK queries states_2 answers_2 i )) ,
  (IntArray.full out_pre (nout + 1 ) (app (answers_2) ((cons (retval) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (nout + 1 ) q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr_2 )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells_2 )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
|--
  EX (cells: (@list (@list (@option Z))))  (answers: (@list Z))  (arr: (@list Z))  (states: (@list (@list Z))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ ((Zlength (kinds)) = q_pre) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6))) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0))))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6)))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= q_pre) ” 
  &&  “ (0 <= (nout + 1 )) ” 
  &&  “ ((nout + 1 ) <= (i + 1 )) ” 
  &&  “ ((nout + 1 ) = (AskCount (queries) ((i + 1 )))) ” 
  &&  “ ((Zlength (states)) = ((i + 1 ) + 1 )) ” 
  &&  “ ((Znth (0) (states) ((@nil Z))) = periods) ” 
  &&  “ (arr = (Znth ((i + 1 )) (states) ((@nil Z)))) ” 
  &&  “ ((Zlength (arr)) = n_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ ((Zlength (answers)) = (nout + 1 )) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr 1 1 n_pre ) ” 
  &&  “ (QueryStepsOK queries states (i + 1 ) ) ” 
  &&  “ (AnswersOK queries states answers (i + 1 ) ) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full out_pre (nout + 1 ) answers )
  **  (IntArray.undef_seg out_pre (nout + 1 ) q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
) \/
(
forall (q_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells_2: (@list (@list (@option Z)))) (answers_2: (@list Z)) (arr_2: (@list Z)) (states_2: (@list (@list Z))) (nout: Z) (i: Z) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr_2) (1) (n_pre) ((Znth i xs 0)) (((Znth i ys 0) - 1 )))) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= (0 + (2 * ((n_pre - 1 ) + 1 ) ) ))) (PreH4 : (0 <= q_pre)) (PreH5 : ((Znth i kinds 0) <> 67)) (PreH6 : (i < q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 100000)) (PreH11 : ((Zlength (periods)) = n_pre)) (PreH12 : ((Zlength (kinds)) = q_pre)) (PreH13 : ((Zlength (xs)) = q_pre)) (PreH14 : ((Zlength (ys)) = q_pre)) (PreH15 : ((Zlength (queries)) = q_pre)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH17 : (PeriodsOK periods )) (PreH18 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH19 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH20 : (0 <= i)) (PreH21 : (i <= q_pre)) (PreH22 : (0 <= nout)) (PreH23 : (nout <= i)) (PreH24 : (nout = (AskCount (queries) (i)))) (PreH25 : ((Zlength (states_2)) = (i + 1 ))) (PreH26 : ((Znth (0) (states_2) ((@nil Z))) = periods)) (PreH27 : (arr_2 = (Znth (i) (states_2) ((@nil Z))))) (PreH28 : ((Zlength (arr_2)) = n_pre)) (PreH29 : (PeriodsOK arr_2 )) (PreH30 : ((Zlength (answers_2)) = nout)) (PreH31 : (CellsShaped cells_2 )) (PreH32 : (TreeOK cells_2 arr_2 1 1 n_pre )) (PreH33 : (QueryStepsOK queries states_2 i )) (PreH34 : (AnswersOK queries states_2 answers_2 i )) ,
  TT && emp 
|--
  EX (states: (@list (@list Z))) ,
  “ ((Znth (i) (states_2) ((@nil Z))) = (Znth ((i + 1 )) (states) ((@nil Z)))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (kinds))) ” 
  &&  “ (0 <= ((AskCount (queries) (i)) + 1 )) ” 
  &&  “ (((AskCount (queries) (i)) + 1 ) <= (i + 1 )) ” 
  &&  “ (((AskCount (queries) (i)) + 1 ) = (AskCount (queries) ((i + 1 )))) ” 
  &&  “ ((Zlength (states)) = ((i + 1 ) + 1 )) ” 
  &&  “ ((Znth (0) (states) ((@nil Z))) = (Znth (0) (states_2) ((@nil Z)))) ” 
  &&  “ ((Zlength ((Znth ((i + 1 )) (states) ((@nil Z))))) = (Zlength ((Znth (0) (states_2) ((@nil Z)))))) ” 
  &&  “ (PeriodsOK (Znth ((i + 1 )) (states) ((@nil Z))) ) ” 
  &&  “ ((Zlength ((app (answers_2) ((cons ((cross ((QuerySlice ((Znth (i) (states_2) ((@nil Z)))) (1) ((Zlength ((Znth (0) (states_2) ((@nil Z)))))) ((Znth i xs 0)) (((Znth i ys 0) - 1 )))) (0))) ((@nil Z))))))) = ((AskCount (queries) (i)) + 1 )) ” 
  &&  “ (TreeOK cells_2 (Znth ((i + 1 )) (states) ((@nil Z))) 1 1 (Zlength ((Znth (0) (states_2) ((@nil Z))))) ) ” 
  &&  “ (QueryStepsOK queries states (i + 1 ) ) ” 
  &&  “ (AnswersOK queries states (app (answers_2) ((cons ((cross ((QuerySlice ((Znth (i) (states_2) ((@nil Z)))) (1) ((Zlength ((Znth (0) (states_2) ((@nil Z)))))) ((Znth i xs 0)) (((Znth i ys 0) - 1 )))) (0))) ((@nil Z))))) (i + 1 ) ) ”
  &&  emp
).

Definition solver_return_wit_1 := 
(
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells_2: (@list (@list (@option Z)))) (answers_2: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i_2: Z) (PreH1 : (i_2 >= q_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= q_pre)) (PreH5 : (q_pre <= 100000)) (PreH6 : ((Zlength (periods)) = n_pre)) (PreH7 : ((Zlength (kinds)) = q_pre)) (PreH8 : ((Zlength (xs)) = q_pre)) (PreH9 : ((Zlength (ys)) = q_pre)) (PreH10 : ((Zlength (queries)) = q_pre)) (PreH11 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH12 : (PeriodsOK periods )) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH14 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH15 : (0 <= i_2)) (PreH16 : (i_2 <= q_pre)) (PreH17 : (0 <= nout)) (PreH18 : (nout <= i_2)) (PreH19 : (nout = (AskCount (queries) (i_2)))) (PreH20 : ((Zlength (states)) = (i_2 + 1 ))) (PreH21 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH22 : (arr = (Znth (i_2) (states) ((@nil Z))))) (PreH23 : ((Zlength (arr)) = n_pre)) (PreH24 : (PeriodsOK arr )) (PreH25 : ((Zlength (answers_2)) = nout)) (PreH26 : (CellsShaped cells_2 )) (PreH27 : (TreeOK cells_2 arr 1 1 n_pre )) (PreH28 : (QueryStepsOK queries states i_2 )) (PreH29 : (AnswersOK queries states answers_2 i_2 )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full out_pre nout answers_2 )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells_2 )
|--
  EX (cells: (@list (@list (@option Z))))  (answers: (@list Z)) ,
  “ (Spec periods queries answers ) ” 
  &&  “ (nout = (Zlength (answers))) ” 
  &&  “ ((Zlength (cells)) = 400020) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < 400020)) -> ((Zlength ((Znth (i) (cells) ((@nil (@option Z)))))) = 60)) ”
  &&  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg_shape ( &( "a_" ) ) 1 (n_pre + 1 ) )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
) \/
(
forall (q_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells_2: (@list (@list (@option Z)))) (answers_2: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i_2: Z) (PreH1 : (i_2 >= q_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= q_pre)) (PreH5 : (q_pre <= 100000)) (PreH6 : ((Zlength (periods)) = n_pre)) (PreH7 : ((Zlength (kinds)) = q_pre)) (PreH8 : ((Zlength (xs)) = q_pre)) (PreH9 : ((Zlength (ys)) = q_pre)) (PreH10 : ((Zlength (queries)) = q_pre)) (PreH11 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH12 : (PeriodsOK periods )) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH14 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH15 : (0 <= i_2)) (PreH16 : (i_2 <= q_pre)) (PreH17 : (0 <= nout)) (PreH18 : (nout <= i_2)) (PreH19 : (nout = (AskCount (queries) (i_2)))) (PreH20 : ((Zlength (states)) = (i_2 + 1 ))) (PreH21 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH22 : (arr = (Znth (i_2) (states) ((@nil Z))))) (PreH23 : ((Zlength (arr)) = n_pre)) (PreH24 : (PeriodsOK arr )) (PreH25 : ((Zlength (answers_2)) = nout)) (PreH26 : (CellsShaped cells_2 )) (PreH27 : (TreeOK cells_2 arr 1 1 n_pre )) (PreH28 : (QueryStepsOK queries states i_2 )) (PreH29 : (AnswersOK queries states answers_2 i_2 )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells_2 )
|--
  EX (cells: (@list (@list (@option Z)))) ,
  “ (Spec periods queries answers_2 ) ” 
  &&  “ (nout = (Zlength (answers_2))) ” 
  &&  “ ((Zlength (cells)) = 400020) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < 400020)) -> ((Zlength ((Znth (i) (cells) ((@nil (@option Z)))))) = 60)) ”
  &&  (IntArray.seg_shape ( &( "a_" ) ) 1 (n_pre + 1 ) )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
).

Definition solver_partial_solve_wit_1 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (periods)))) (PreH4 : (1 <= q_pre)) (PreH5 : (q_pre <= 100000)) (PreH6 : (q_pre = (Zlength (kinds)))) (PreH7 : ((Zlength (xs)) = q_pre)) (PreH8 : ((Zlength (ys)) = q_pre)) (PreH9 : ((Zlength (queries)) = q_pre)) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i periods 0)) /\ ((Znth i periods 0) <= 6)))) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < q_pre)) -> ((Znth (i_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth i_2 kinds 0)) ((Znth i_2 xs 0)))) ((Znth i_2 ys 0)))))) (PreH12 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < q_pre)) -> ((((((Znth i_3 kinds 0) = 65) /\ (1 <= (Znth i_3 xs 0))) /\ ((Znth i_3 xs 0) < (Znth i_3 ys 0))) /\ ((Znth i_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth i_3 kinds 0) = 67) /\ (1 <= (Znth i_3 xs 0))) /\ ((Znth i_3 xs 0) <= n_pre)) /\ (2 <= (Znth i_3 ys 0))) /\ ((Znth i_3 ys 0) <= 6))))) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
  **  (IntArray.undef_seg ( &( "a_" ) ) 1 (n_pre + 1 ) )
  **  (IntArray2.undef_full ( &( "seg" ) ) 400020 60 )
|--
  “ (0 <= q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (periods))) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ (q_pre = (Zlength (kinds))) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((2 <= (Znth i periods 0)) /\ ((Znth i periods 0) <= 6))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < q_pre)) -> ((Znth (i_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth i_2 kinds 0)) ((Znth i_2 xs 0)))) ((Znth i_2 ys 0))))) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < q_pre)) -> ((((((Znth i_3 kinds 0) = 65) /\ (1 <= (Znth i_3 xs 0))) /\ ((Znth i_3 xs 0) < (Znth i_3 ys 0))) /\ ((Znth i_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth i_3 kinds 0) = 67) /\ (1 <= (Znth i_3 xs 0))) /\ ((Znth i_3 xs 0) <= n_pre)) /\ (2 <= (Znth i_3 ys 0))) /\ ((Znth i_3 ys 0) <= 6)))) ”
  &&  (IntArray2.undef_full ( &( "seg" ) ) 400020 60 )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
  **  (IntArray.undef_seg ( &( "a_" ) ) 1 (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_2 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0: (@list (@list (@option Z)))) (copied: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= q_pre)) (PreH5 : (q_pre <= 100000)) (PreH6 : ((Zlength (periods)) = n_pre)) (PreH7 : ((Zlength (kinds)) = q_pre)) (PreH8 : ((Zlength (xs)) = q_pre)) (PreH9 : ((Zlength (ys)) = q_pre)) (PreH10 : ((Zlength (queries)) = q_pre)) (PreH11 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH12 : (PeriodsOK periods )) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH14 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH15 : (1 <= i)) (PreH16 : (i <= (n_pre + 1 ))) (PreH17 : (copied = (NodeSlice (periods) (1) ((i - 1 ))))) (PreH18 : (CellsShaped cells0 )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.seg ( &( "a_" ) ) 1 i copied )
  **  (IntArray.undef_seg ( &( "a_" ) ) i (n_pre + 1 ) )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0 )
|--
  “ (0 <= q_pre) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ ((Zlength (kinds)) = q_pre) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6))) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0))))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (copied = (NodeSlice (periods) (1) ((i - 1 )))) ” 
  &&  “ (CellsShaped cells0 ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) periods 0))
  **  (IntArray.missing_i a_pre i 1 (n_pre + 1 ) periods )
  **  (IntArray.seg ( &( "a_" ) ) 1 i copied )
  **  (IntArray.undef_seg ( &( "a_" ) ) i (n_pre + 1 ) )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0 )
.

Definition solver_partial_solve_wit_3 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0: (@list (@list (@option Z)))) (copied: (@list Z)) (i: Z) (PreH1 : (0 <= q_pre)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= q_pre)) (PreH6 : (q_pre <= 100000)) (PreH7 : ((Zlength (periods)) = n_pre)) (PreH8 : ((Zlength (kinds)) = q_pre)) (PreH9 : ((Zlength (xs)) = q_pre)) (PreH10 : ((Zlength (ys)) = q_pre)) (PreH11 : ((Zlength (queries)) = q_pre)) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH13 : (PeriodsOK periods )) (PreH14 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH15 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH16 : (1 <= i)) (PreH17 : (i <= (n_pre + 1 ))) (PreH18 : (copied = (NodeSlice (periods) (1) ((i - 1 ))))) (PreH19 : (CellsShaped cells0 )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.seg ( &( "a_" ) ) 1 i copied )
  **  (IntArray.undef_seg ( &( "a_" ) ) i (n_pre + 1 ) )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0 )
|--
  “ (0 <= q_pre) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ ((Zlength (kinds)) = q_pre) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6))) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0))))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6)))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (copied = (NodeSlice (periods) (1) ((i - 1 )))) ” 
  &&  “ (CellsShaped cells0 ) ”
  &&  (((( &( "a_" ) ) + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "a_" ) ) (i + 1 ) (n_pre + 1 ) )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.seg ( &( "a_" ) ) 1 i copied )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0 )
.

Definition solver_partial_solve_wit_4_pure := 
(
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0: (@list (@list (@option Z)))) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= q_pre)) (PreH4 : (q_pre <= 100000)) (PreH5 : ((Zlength (periods)) = n_pre)) (PreH6 : ((Zlength (kinds)) = q_pre)) (PreH7 : ((Zlength (xs)) = q_pre)) (PreH8 : ((Zlength (ys)) = q_pre)) (PreH9 : ((Zlength (queries)) = q_pre)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH11 : (PeriodsOK periods )) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH13 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH14 : (CellsShaped cells0 )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0 )
|--
  “ (n_pre <= n_pre) ” 
  &&  “ (n_pre = (Zlength (periods))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ (CellsShaped cells0 ) ” 
  &&  “ (NodeFits 1 1 n_pre ) ”
) \/
(
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0: (@list (@list (@option Z)))) (PreH1 : (q_pre <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (q_pre >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (0 <= q_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= 100000)) (PreH10 : ((Zlength (periods)) = n_pre)) (PreH11 : ((Zlength (kinds)) = q_pre)) (PreH12 : ((Zlength (xs)) = q_pre)) (PreH13 : ((Zlength (ys)) = q_pre)) (PreH14 : ((Zlength (queries)) = q_pre)) (PreH15 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH16 : (PeriodsOK periods )) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH18 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH19 : (CellsShaped cells0 )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0 )
|--
  “ (NodeFits 1 1 n_pre ) ”
).

Definition solver_partial_solve_wit_4_pure_split_goal_1 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0: (@list (@list (@option Z)))) (PreH1 : (q_pre <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (q_pre >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (0 <= q_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= 100000)) (PreH10 : ((Zlength (periods)) = n_pre)) (PreH11 : ((Zlength (kinds)) = q_pre)) (PreH12 : ((Zlength (xs)) = q_pre)) (PreH13 : ((Zlength (ys)) = q_pre)) (PreH14 : ((Zlength (queries)) = q_pre)) (PreH15 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH16 : (PeriodsOK periods )) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH18 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH19 : (CellsShaped cells0 )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0 )
|--
  “ (NodeFits 1 1 n_pre ) ”
.

Definition solver_partial_solve_wit_4_aux := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells0: (@list (@list (@option Z)))) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= q_pre)) (PreH4 : (q_pre <= 100000)) (PreH5 : ((Zlength (periods)) = n_pre)) (PreH6 : ((Zlength (kinds)) = q_pre)) (PreH7 : ((Zlength (xs)) = q_pre)) (PreH8 : ((Zlength (ys)) = q_pre)) (PreH9 : ((Zlength (queries)) = q_pre)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH11 : (PeriodsOK periods )) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH13 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH14 : (CellsShaped cells0 )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0 )
|--
  “ (n_pre <= n_pre) ” 
  &&  “ (n_pre = (Zlength (periods))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ (CellsShaped cells0 ) ” 
  &&  “ (NodeFits 1 1 n_pre ) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ ((Zlength (kinds)) = q_pre) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6))) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0))))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6)))) ” 
  &&  “ (CellsShaped cells0 ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) periods )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0 )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.undef_full out_pre q_pre )
.

Definition solver_partial_solve_wit_4 := solver_partial_solve_wit_4_pure -> solver_partial_solve_wit_4_aux.

Definition solver_partial_solve_wit_5 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (i < q_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= q_pre)) (PreH5 : (q_pre <= 100000)) (PreH6 : ((Zlength (periods)) = n_pre)) (PreH7 : ((Zlength (kinds)) = q_pre)) (PreH8 : ((Zlength (xs)) = q_pre)) (PreH9 : ((Zlength (ys)) = q_pre)) (PreH10 : ((Zlength (queries)) = q_pre)) (PreH11 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH12 : (PeriodsOK periods )) (PreH13 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH14 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH15 : (0 <= i)) (PreH16 : (i <= q_pre)) (PreH17 : (0 <= nout)) (PreH18 : (nout <= i)) (PreH19 : (nout = (AskCount (queries) (i)))) (PreH20 : ((Zlength (states)) = (i + 1 ))) (PreH21 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH22 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH23 : ((Zlength (arr)) = n_pre)) (PreH24 : (PeriodsOK arr )) (PreH25 : ((Zlength (answers)) = nout)) (PreH26 : (CellsShaped cells )) (PreH27 : (TreeOK cells arr 1 1 n_pre )) (PreH28 : (QueryStepsOK queries states i )) (PreH29 : (AnswersOK queries states answers i )) ,
  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (i < q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ ((Zlength (kinds)) = q_pre) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6))) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0))))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (0 <= nout) ” 
  &&  “ (nout <= i) ” 
  &&  “ (nout = (AskCount (queries) (i))) ” 
  &&  “ ((Zlength (states)) = (i + 1 )) ” 
  &&  “ ((Znth (0) (states) ((@nil Z))) = periods) ” 
  &&  “ (arr = (Znth (i) (states) ((@nil Z)))) ” 
  &&  “ ((Zlength (arr)) = n_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ ((Zlength (answers)) = nout) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr 1 1 n_pre ) ” 
  &&  “ (QueryStepsOK queries states i ) ” 
  &&  “ (AnswersOK queries states answers i ) ”
  &&  (((type_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i kinds 0))
  **  (CharArray.missing_i type_pre i 0 q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
.

Definition solver_partial_solve_wit_6 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : ((Znth i kinds 0) = 67)) (PreH2 : (i < q_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= q_pre)) (PreH6 : (q_pre <= 100000)) (PreH7 : ((Zlength (periods)) = n_pre)) (PreH8 : ((Zlength (kinds)) = q_pre)) (PreH9 : ((Zlength (xs)) = q_pre)) (PreH10 : ((Zlength (ys)) = q_pre)) (PreH11 : ((Zlength (queries)) = q_pre)) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH13 : (PeriodsOK periods )) (PreH14 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH15 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH16 : (0 <= i)) (PreH17 : (i <= q_pre)) (PreH18 : (0 <= nout)) (PreH19 : (nout <= i)) (PreH20 : (nout = (AskCount (queries) (i)))) (PreH21 : ((Zlength (states)) = (i + 1 ))) (PreH22 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH23 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH24 : ((Zlength (arr)) = n_pre)) (PreH25 : (PeriodsOK arr )) (PreH26 : ((Zlength (answers)) = nout)) (PreH27 : (CellsShaped cells )) (PreH28 : (TreeOK cells arr 1 1 n_pre )) (PreH29 : (QueryStepsOK queries states i )) (PreH30 : (AnswersOK queries states answers i )) ,
  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (0 <= q_pre) ” 
  &&  “ ((Znth i kinds 0) = 67) ” 
  &&  “ (i < q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ ((Zlength (kinds)) = q_pre) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6))) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0))))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (0 <= nout) ” 
  &&  “ (nout <= i) ” 
  &&  “ (nout = (AskCount (queries) (i))) ” 
  &&  “ ((Zlength (states)) = (i + 1 )) ” 
  &&  “ ((Znth (0) (states) ((@nil Z))) = periods) ” 
  &&  “ (arr = (Znth (i) (states) ((@nil Z)))) ” 
  &&  “ ((Zlength (arr)) = n_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ ((Zlength (answers)) = nout) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr 1 1 n_pre ) ” 
  &&  “ (QueryStepsOK queries states i ) ” 
  &&  “ (AnswersOK queries states answers i ) ”
  &&  (((qx_pre + (i * sizeof(INT)))) # Int  |-> (Znth i xs 0))
  **  (IntArray.missing_i qx_pre i 0 q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
.

Definition solver_partial_solve_wit_7 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (0 <= q_pre)) (PreH2 : ((Znth i kinds 0) = 67)) (PreH3 : (i < q_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 100000)) (PreH8 : ((Zlength (periods)) = n_pre)) (PreH9 : ((Zlength (kinds)) = q_pre)) (PreH10 : ((Zlength (xs)) = q_pre)) (PreH11 : ((Zlength (ys)) = q_pre)) (PreH12 : ((Zlength (queries)) = q_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH14 : (PeriodsOK periods )) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH16 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH17 : (0 <= i)) (PreH18 : (i <= q_pre)) (PreH19 : (0 <= nout)) (PreH20 : (nout <= i)) (PreH21 : (nout = (AskCount (queries) (i)))) (PreH22 : ((Zlength (states)) = (i + 1 ))) (PreH23 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH24 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH25 : ((Zlength (arr)) = n_pre)) (PreH26 : (PeriodsOK arr )) (PreH27 : ((Zlength (answers)) = nout)) (PreH28 : (CellsShaped cells )) (PreH29 : (TreeOK cells arr 1 1 n_pre )) (PreH30 : (QueryStepsOK queries states i )) (PreH31 : (AnswersOK queries states answers i )) ,
  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (0 <= q_pre) ” 
  &&  “ ((Znth i kinds 0) = 67) ” 
  &&  “ (i < q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ ((Zlength (kinds)) = q_pre) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6))) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0))))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (0 <= nout) ” 
  &&  “ (nout <= i) ” 
  &&  “ (nout = (AskCount (queries) (i))) ” 
  &&  “ ((Zlength (states)) = (i + 1 )) ” 
  &&  “ ((Znth (0) (states) ((@nil Z))) = periods) ” 
  &&  “ (arr = (Znth (i) (states) ((@nil Z)))) ” 
  &&  “ ((Zlength (arr)) = n_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ ((Zlength (answers)) = nout) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr 1 1 n_pre ) ” 
  &&  “ (QueryStepsOK queries states i ) ” 
  &&  “ (AnswersOK queries states answers i ) ”
  &&  (((qy_pre + (i * sizeof(INT)))) # Int  |-> (Znth i ys 0))
  **  (IntArray.missing_i qy_pre i 0 q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
.

Definition solver_partial_solve_wit_8 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (0 <= q_pre)) (PreH2 : ((Znth i kinds 0) = 67)) (PreH3 : (i < q_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 100000)) (PreH8 : ((Zlength (periods)) = n_pre)) (PreH9 : ((Zlength (kinds)) = q_pre)) (PreH10 : ((Zlength (xs)) = q_pre)) (PreH11 : ((Zlength (ys)) = q_pre)) (PreH12 : ((Zlength (queries)) = q_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH14 : (PeriodsOK periods )) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH16 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH17 : (0 <= i)) (PreH18 : (i <= q_pre)) (PreH19 : (0 <= nout)) (PreH20 : (nout <= i)) (PreH21 : (nout = (AskCount (queries) (i)))) (PreH22 : ((Zlength (states)) = (i + 1 ))) (PreH23 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH24 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH25 : ((Zlength (arr)) = n_pre)) (PreH26 : (PeriodsOK arr )) (PreH27 : ((Zlength (answers)) = nout)) (PreH28 : (CellsShaped cells )) (PreH29 : (TreeOK cells arr 1 1 n_pre )) (PreH30 : (QueryStepsOK queries states i )) (PreH31 : (AnswersOK queries states answers i )) ,
  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (0 <= q_pre) ” 
  &&  “ ((Znth i kinds 0) = 67) ” 
  &&  “ (i < q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ ((Zlength (kinds)) = q_pre) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6))) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0))))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (0 <= nout) ” 
  &&  “ (nout <= i) ” 
  &&  “ (nout = (AskCount (queries) (i))) ” 
  &&  “ ((Zlength (states)) = (i + 1 )) ” 
  &&  “ ((Znth (0) (states) ((@nil Z))) = periods) ” 
  &&  “ (arr = (Znth (i) (states) ((@nil Z)))) ” 
  &&  “ ((Zlength (arr)) = n_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ ((Zlength (answers)) = nout) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr 1 1 n_pre ) ” 
  &&  “ (QueryStepsOK queries states i ) ” 
  &&  “ (AnswersOK queries states answers i ) ”
  &&  (((( &( "a_" ) ) + ((Znth i xs 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "a_" ) ) (Znth i xs 0) 1 (n_pre + 1 ) arr )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
.

Definition solver_partial_solve_wit_9 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (0 <= q_pre)) (PreH2 : ((Znth i kinds 0) = 67)) (PreH3 : (i < q_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 100000)) (PreH8 : ((Zlength (periods)) = n_pre)) (PreH9 : ((Zlength (kinds)) = q_pre)) (PreH10 : ((Zlength (xs)) = q_pre)) (PreH11 : ((Zlength (ys)) = q_pre)) (PreH12 : ((Zlength (queries)) = q_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH14 : (PeriodsOK periods )) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH16 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH17 : (0 <= i)) (PreH18 : (i <= q_pre)) (PreH19 : (0 <= nout)) (PreH20 : (nout <= i)) (PreH21 : (nout = (AskCount (queries) (i)))) (PreH22 : ((Zlength (states)) = (i + 1 ))) (PreH23 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH24 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH25 : ((Zlength (arr)) = n_pre)) (PreH26 : (PeriodsOK arr )) (PreH27 : ((Zlength (answers)) = nout)) (PreH28 : (CellsShaped cells )) (PreH29 : (TreeOK cells arr 1 1 n_pre )) (PreH30 : (QueryStepsOK queries states i )) (PreH31 : (AnswersOK queries states answers i )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (0 <= q_pre) ” 
  &&  “ ((Znth i kinds 0) = 67) ” 
  &&  “ (i < q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ ((Zlength (kinds)) = q_pre) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6))) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0))))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (0 <= nout) ” 
  &&  “ (nout <= i) ” 
  &&  “ (nout = (AskCount (queries) (i))) ” 
  &&  “ ((Zlength (states)) = (i + 1 )) ” 
  &&  “ ((Znth (0) (states) ((@nil Z))) = periods) ” 
  &&  “ (arr = (Znth (i) (states) ((@nil Z)))) ” 
  &&  “ ((Zlength (arr)) = n_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ ((Zlength (answers)) = nout) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr 1 1 n_pre ) ” 
  &&  “ (QueryStepsOK queries states i ) ” 
  &&  “ (AnswersOK queries states answers i ) ”
  &&  (((qx_pre + (i * sizeof(INT)))) # Int  |-> (Znth i xs 0))
  **  (IntArray.missing_i qx_pre i 0 q_pre xs )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) )
  **  (IntArray.full qy_pre q_pre ys )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
.

Definition solver_partial_solve_wit_10_pure := 
(
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (0 <= q_pre)) (PreH2 : ((Znth i kinds 0) = 67)) (PreH3 : (i < q_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 100000)) (PreH8 : ((Zlength (periods)) = n_pre)) (PreH9 : ((Zlength (kinds)) = q_pre)) (PreH10 : ((Zlength (xs)) = q_pre)) (PreH11 : ((Zlength (ys)) = q_pre)) (PreH12 : ((Zlength (queries)) = q_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH14 : (PeriodsOK periods )) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH16 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH17 : (0 <= i)) (PreH18 : (i <= q_pre)) (PreH19 : (0 <= nout)) (PreH20 : (nout <= i)) (PreH21 : (nout = (AskCount (queries) (i)))) (PreH22 : ((Zlength (states)) = (i + 1 ))) (PreH23 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH24 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH25 : ((Zlength (arr)) = n_pre)) (PreH26 : (PeriodsOK arr )) (PreH27 : ((Zlength (answers)) = nout)) (PreH28 : (CellsShaped cells )) (PreH29 : (TreeOK cells arr 1 1 n_pre )) (PreH30 : (QueryStepsOK queries states i )) (PreH31 : (AnswersOK queries states answers i )) ,
  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) )
  **  (IntArray.full qy_pre q_pre ys )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits 1 1 n_pre ) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (n_pre = (Zlength ((replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr))))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= (Znth i xs 0)) ” 
  &&  “ ((Znth i xs 0) <= n_pre) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeStaleAt cells (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) 1 1 n_pre (Znth i xs 0) ) ” 
  &&  “ (TreeStaleAt cells (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) 1 1 (Zlength (periods)) (Znth i xs 0) ) ” 
  &&  “ (PeriodsOK (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) ) ” 
  &&  “ ((Znth i xs 0) <= (Zlength (periods))) ” 
  &&  “ ((Zlength (periods)) = (Zlength ((replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr))))) ” 
  &&  “ (NodeFits 1 1 (Zlength (periods)) ) ”
) \/
(
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (nout <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (nout >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (0 <= q_pre)) (PreH10 : ((Znth i kinds 0) = 67)) (PreH11 : (i < q_pre)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 100000)) (PreH16 : ((Zlength (periods)) = n_pre)) (PreH17 : ((Zlength (kinds)) = q_pre)) (PreH18 : ((Zlength (xs)) = q_pre)) (PreH19 : ((Zlength (ys)) = q_pre)) (PreH20 : ((Zlength (queries)) = q_pre)) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH22 : (PeriodsOK periods )) (PreH23 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH24 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH25 : (0 <= i)) (PreH26 : (i <= q_pre)) (PreH27 : (0 <= nout)) (PreH28 : (nout <= i)) (PreH29 : (nout = (AskCount (queries) (i)))) (PreH30 : ((Zlength (states)) = (i + 1 ))) (PreH31 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH32 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH33 : ((Zlength (arr)) = n_pre)) (PreH34 : (PeriodsOK arr )) (PreH35 : ((Zlength (answers)) = nout)) (PreH36 : (CellsShaped cells )) (PreH37 : (TreeOK cells arr 1 1 n_pre )) (PreH38 : (QueryStepsOK queries states i )) (PreH39 : (AnswersOK queries states answers i )) ,
  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) )
  **  (IntArray.full qy_pre q_pre ys )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits 1 1 n_pre ) ” 
  &&  “ (n_pre = (Zlength ((replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr))))) ” 
  &&  “ (PeriodsOK (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) ) ” 
  &&  “ (TreeStaleAt cells (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) 1 1 n_pre (Znth i xs 0) ) ” 
  &&  “ (TreeStaleAt cells (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) 1 1 n_pre (Znth i xs 0) ) ” 
  &&  “ (n_pre = (Zlength ((replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr))))) ” 
  &&  “ (NodeFits 1 1 n_pre ) ”
).

Definition solver_partial_solve_wit_10_pure_split_goal_1 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (nout <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (nout >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (0 <= q_pre)) (PreH10 : ((Znth i kinds 0) = 67)) (PreH11 : (i < q_pre)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 100000)) (PreH16 : ((Zlength (periods)) = n_pre)) (PreH17 : ((Zlength (kinds)) = q_pre)) (PreH18 : ((Zlength (xs)) = q_pre)) (PreH19 : ((Zlength (ys)) = q_pre)) (PreH20 : ((Zlength (queries)) = q_pre)) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH22 : (PeriodsOK periods )) (PreH23 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH24 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH25 : (0 <= i)) (PreH26 : (i <= q_pre)) (PreH27 : (0 <= nout)) (PreH28 : (nout <= i)) (PreH29 : (nout = (AskCount (queries) (i)))) (PreH30 : ((Zlength (states)) = (i + 1 ))) (PreH31 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH32 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH33 : ((Zlength (arr)) = n_pre)) (PreH34 : (PeriodsOK arr )) (PreH35 : ((Zlength (answers)) = nout)) (PreH36 : (CellsShaped cells )) (PreH37 : (TreeOK cells arr 1 1 n_pre )) (PreH38 : (QueryStepsOK queries states i )) (PreH39 : (AnswersOK queries states answers i )) ,
  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) )
  **  (IntArray.full qy_pre q_pre ys )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits 1 1 n_pre ) ”
.

Definition solver_partial_solve_wit_10_pure_split_goal_2 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (nout <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (nout >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (0 <= q_pre)) (PreH10 : ((Znth i kinds 0) = 67)) (PreH11 : (i < q_pre)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 100000)) (PreH16 : ((Zlength (periods)) = n_pre)) (PreH17 : ((Zlength (kinds)) = q_pre)) (PreH18 : ((Zlength (xs)) = q_pre)) (PreH19 : ((Zlength (ys)) = q_pre)) (PreH20 : ((Zlength (queries)) = q_pre)) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH22 : (PeriodsOK periods )) (PreH23 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH24 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH25 : (0 <= i)) (PreH26 : (i <= q_pre)) (PreH27 : (0 <= nout)) (PreH28 : (nout <= i)) (PreH29 : (nout = (AskCount (queries) (i)))) (PreH30 : ((Zlength (states)) = (i + 1 ))) (PreH31 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH32 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH33 : ((Zlength (arr)) = n_pre)) (PreH34 : (PeriodsOK arr )) (PreH35 : ((Zlength (answers)) = nout)) (PreH36 : (CellsShaped cells )) (PreH37 : (TreeOK cells arr 1 1 n_pre )) (PreH38 : (QueryStepsOK queries states i )) (PreH39 : (AnswersOK queries states answers i )) ,
  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) )
  **  (IntArray.full qy_pre q_pre ys )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (n_pre = (Zlength ((replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr))))) ”
.

Definition solver_partial_solve_wit_10_pure_split_goal_3 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (nout <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (nout >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (0 <= q_pre)) (PreH10 : ((Znth i kinds 0) = 67)) (PreH11 : (i < q_pre)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 100000)) (PreH16 : ((Zlength (periods)) = n_pre)) (PreH17 : ((Zlength (kinds)) = q_pre)) (PreH18 : ((Zlength (xs)) = q_pre)) (PreH19 : ((Zlength (ys)) = q_pre)) (PreH20 : ((Zlength (queries)) = q_pre)) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH22 : (PeriodsOK periods )) (PreH23 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH24 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH25 : (0 <= i)) (PreH26 : (i <= q_pre)) (PreH27 : (0 <= nout)) (PreH28 : (nout <= i)) (PreH29 : (nout = (AskCount (queries) (i)))) (PreH30 : ((Zlength (states)) = (i + 1 ))) (PreH31 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH32 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH33 : ((Zlength (arr)) = n_pre)) (PreH34 : (PeriodsOK arr )) (PreH35 : ((Zlength (answers)) = nout)) (PreH36 : (CellsShaped cells )) (PreH37 : (TreeOK cells arr 1 1 n_pre )) (PreH38 : (QueryStepsOK queries states i )) (PreH39 : (AnswersOK queries states answers i )) ,
  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) )
  **  (IntArray.full qy_pre q_pre ys )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (PeriodsOK (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) ) ”
.

Definition solver_partial_solve_wit_10_pure_split_goal_4 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (nout <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (nout >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (0 <= q_pre)) (PreH10 : ((Znth i kinds 0) = 67)) (PreH11 : (i < q_pre)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 100000)) (PreH16 : ((Zlength (periods)) = n_pre)) (PreH17 : ((Zlength (kinds)) = q_pre)) (PreH18 : ((Zlength (xs)) = q_pre)) (PreH19 : ((Zlength (ys)) = q_pre)) (PreH20 : ((Zlength (queries)) = q_pre)) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH22 : (PeriodsOK periods )) (PreH23 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH24 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH25 : (0 <= i)) (PreH26 : (i <= q_pre)) (PreH27 : (0 <= nout)) (PreH28 : (nout <= i)) (PreH29 : (nout = (AskCount (queries) (i)))) (PreH30 : ((Zlength (states)) = (i + 1 ))) (PreH31 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH32 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH33 : ((Zlength (arr)) = n_pre)) (PreH34 : (PeriodsOK arr )) (PreH35 : ((Zlength (answers)) = nout)) (PreH36 : (CellsShaped cells )) (PreH37 : (TreeOK cells arr 1 1 n_pre )) (PreH38 : (QueryStepsOK queries states i )) (PreH39 : (AnswersOK queries states answers i )) ,
  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) )
  **  (IntArray.full qy_pre q_pre ys )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (TreeStaleAt cells (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) 1 1 n_pre (Znth i xs 0) ) ”
.

Definition solver_partial_solve_wit_10_pure_split_goal_5 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (nout <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (nout >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (0 <= q_pre)) (PreH10 : ((Znth i kinds 0) = 67)) (PreH11 : (i < q_pre)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 100000)) (PreH16 : ((Zlength (periods)) = n_pre)) (PreH17 : ((Zlength (kinds)) = q_pre)) (PreH18 : ((Zlength (xs)) = q_pre)) (PreH19 : ((Zlength (ys)) = q_pre)) (PreH20 : ((Zlength (queries)) = q_pre)) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH22 : (PeriodsOK periods )) (PreH23 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH24 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH25 : (0 <= i)) (PreH26 : (i <= q_pre)) (PreH27 : (0 <= nout)) (PreH28 : (nout <= i)) (PreH29 : (nout = (AskCount (queries) (i)))) (PreH30 : ((Zlength (states)) = (i + 1 ))) (PreH31 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH32 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH33 : ((Zlength (arr)) = n_pre)) (PreH34 : (PeriodsOK arr )) (PreH35 : ((Zlength (answers)) = nout)) (PreH36 : (CellsShaped cells )) (PreH37 : (TreeOK cells arr 1 1 n_pre )) (PreH38 : (QueryStepsOK queries states i )) (PreH39 : (AnswersOK queries states answers i )) ,
  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) )
  **  (IntArray.full qy_pre q_pre ys )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (TreeStaleAt cells (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) 1 1 n_pre (Znth i xs 0) ) ”
.

Definition solver_partial_solve_wit_10_pure_split_goal_6 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (nout <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (nout >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (0 <= q_pre)) (PreH10 : ((Znth i kinds 0) = 67)) (PreH11 : (i < q_pre)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 100000)) (PreH16 : ((Zlength (periods)) = n_pre)) (PreH17 : ((Zlength (kinds)) = q_pre)) (PreH18 : ((Zlength (xs)) = q_pre)) (PreH19 : ((Zlength (ys)) = q_pre)) (PreH20 : ((Zlength (queries)) = q_pre)) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH22 : (PeriodsOK periods )) (PreH23 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH24 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH25 : (0 <= i)) (PreH26 : (i <= q_pre)) (PreH27 : (0 <= nout)) (PreH28 : (nout <= i)) (PreH29 : (nout = (AskCount (queries) (i)))) (PreH30 : ((Zlength (states)) = (i + 1 ))) (PreH31 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH32 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH33 : ((Zlength (arr)) = n_pre)) (PreH34 : (PeriodsOK arr )) (PreH35 : ((Zlength (answers)) = nout)) (PreH36 : (CellsShaped cells )) (PreH37 : (TreeOK cells arr 1 1 n_pre )) (PreH38 : (QueryStepsOK queries states i )) (PreH39 : (AnswersOK queries states answers i )) ,
  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) )
  **  (IntArray.full qy_pre q_pre ys )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (n_pre = (Zlength ((replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr))))) ”
.

Definition solver_partial_solve_wit_10_pure_split_goal_7 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (nout <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (nout >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (0 <= q_pre)) (PreH10 : ((Znth i kinds 0) = 67)) (PreH11 : (i < q_pre)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 100000)) (PreH16 : ((Zlength (periods)) = n_pre)) (PreH17 : ((Zlength (kinds)) = q_pre)) (PreH18 : ((Zlength (xs)) = q_pre)) (PreH19 : ((Zlength (ys)) = q_pre)) (PreH20 : ((Zlength (queries)) = q_pre)) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH22 : (PeriodsOK periods )) (PreH23 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH24 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH25 : (0 <= i)) (PreH26 : (i <= q_pre)) (PreH27 : (0 <= nout)) (PreH28 : (nout <= i)) (PreH29 : (nout = (AskCount (queries) (i)))) (PreH30 : ((Zlength (states)) = (i + 1 ))) (PreH31 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH32 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH33 : ((Zlength (arr)) = n_pre)) (PreH34 : (PeriodsOK arr )) (PreH35 : ((Zlength (answers)) = nout)) (PreH36 : (CellsShaped cells )) (PreH37 : (TreeOK cells arr 1 1 n_pre )) (PreH38 : (QueryStepsOK queries states i )) (PreH39 : (AnswersOK queries states answers i )) ,
  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) )
  **  (IntArray.full qy_pre q_pre ys )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits 1 1 n_pre ) ”
.

Definition solver_partial_solve_wit_10_aux := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (0 <= q_pre)) (PreH2 : ((Znth i kinds 0) = 67)) (PreH3 : (i < q_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 100000)) (PreH8 : ((Zlength (periods)) = n_pre)) (PreH9 : ((Zlength (kinds)) = q_pre)) (PreH10 : ((Zlength (xs)) = q_pre)) (PreH11 : ((Zlength (ys)) = q_pre)) (PreH12 : ((Zlength (queries)) = q_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH14 : (PeriodsOK periods )) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH16 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH17 : (0 <= i)) (PreH18 : (i <= q_pre)) (PreH19 : (0 <= nout)) (PreH20 : (nout <= i)) (PreH21 : (nout = (AskCount (queries) (i)))) (PreH22 : ((Zlength (states)) = (i + 1 ))) (PreH23 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH24 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH25 : ((Zlength (arr)) = n_pre)) (PreH26 : (PeriodsOK arr )) (PreH27 : ((Zlength (answers)) = nout)) (PreH28 : (CellsShaped cells )) (PreH29 : (TreeOK cells arr 1 1 n_pre )) (PreH30 : (QueryStepsOK queries states i )) (PreH31 : (AnswersOK queries states answers i )) ,
  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) )
  **  (IntArray.full qy_pre q_pre ys )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits 1 1 n_pre ) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (n_pre = (Zlength ((replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr))))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= (Znth i xs 0)) ” 
  &&  “ ((Znth i xs 0) <= n_pre) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeStaleAt cells (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) 1 1 n_pre (Znth i xs 0) ) ” 
  &&  “ (TreeStaleAt cells (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) 1 1 (Zlength (periods)) (Znth i xs 0) ) ” 
  &&  “ (PeriodsOK (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) ) ” 
  &&  “ ((Znth i xs 0) <= (Zlength (periods))) ” 
  &&  “ ((Zlength (periods)) = (Zlength ((replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr))))) ” 
  &&  “ (NodeFits 1 1 (Zlength (periods)) ) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ ((Znth i kinds 0) = 67) ” 
  &&  “ (i < q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ ((Zlength (kinds)) = q_pre) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6))) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0))))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (0 <= nout) ” 
  &&  “ (nout <= i) ” 
  &&  “ (nout = (AskCount (queries) (i))) ” 
  &&  “ ((Zlength (states)) = (i + 1 )) ” 
  &&  “ ((Znth (0) (states) ((@nil Z))) = periods) ” 
  &&  “ (arr = (Znth (i) (states) ((@nil Z)))) ” 
  &&  “ ((Zlength (arr)) = n_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ ((Zlength (answers)) = nout) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr 1 1 n_pre ) ” 
  &&  “ (QueryStepsOK queries states i ) ” 
  &&  “ (AnswersOK queries states answers i ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) (replace_Znth (((Znth i xs 0) - 1 )) ((Znth i ys 0)) (arr)) )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
.

Definition solver_partial_solve_wit_10 := solver_partial_solve_wit_10_pure -> solver_partial_solve_wit_10_aux.

Definition solver_partial_solve_wit_11 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : ((Znth i kinds 0) <> 67)) (PreH2 : (i < q_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= q_pre)) (PreH6 : (q_pre <= 100000)) (PreH7 : ((Zlength (periods)) = n_pre)) (PreH8 : ((Zlength (kinds)) = q_pre)) (PreH9 : ((Zlength (xs)) = q_pre)) (PreH10 : ((Zlength (ys)) = q_pre)) (PreH11 : ((Zlength (queries)) = q_pre)) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH13 : (PeriodsOK periods )) (PreH14 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH15 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH16 : (0 <= i)) (PreH17 : (i <= q_pre)) (PreH18 : (0 <= nout)) (PreH19 : (nout <= i)) (PreH20 : (nout = (AskCount (queries) (i)))) (PreH21 : ((Zlength (states)) = (i + 1 ))) (PreH22 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH23 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH24 : ((Zlength (arr)) = n_pre)) (PreH25 : (PeriodsOK arr )) (PreH26 : ((Zlength (answers)) = nout)) (PreH27 : (CellsShaped cells )) (PreH28 : (TreeOK cells arr 1 1 n_pre )) (PreH29 : (QueryStepsOK queries states i )) (PreH30 : (AnswersOK queries states answers i )) ,
  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full qx_pre q_pre xs )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (0 <= q_pre) ” 
  &&  “ ((Znth i kinds 0) <> 67) ” 
  &&  “ (i < q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ ((Zlength (kinds)) = q_pre) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6))) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0))))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (0 <= nout) ” 
  &&  “ (nout <= i) ” 
  &&  “ (nout = (AskCount (queries) (i))) ” 
  &&  “ ((Zlength (states)) = (i + 1 )) ” 
  &&  “ ((Znth (0) (states) ((@nil Z))) = periods) ” 
  &&  “ (arr = (Znth (i) (states) ((@nil Z)))) ” 
  &&  “ ((Zlength (arr)) = n_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ ((Zlength (answers)) = nout) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr 1 1 n_pre ) ” 
  &&  “ (QueryStepsOK queries states i ) ” 
  &&  “ (AnswersOK queries states answers i ) ”
  &&  (((qx_pre + (i * sizeof(INT)))) # Int  |-> (Znth i xs 0))
  **  (IntArray.missing_i qx_pre i 0 q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
.

Definition solver_partial_solve_wit_12 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (0 <= q_pre)) (PreH2 : ((Znth i kinds 0) <> 67)) (PreH3 : (i < q_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 100000)) (PreH8 : ((Zlength (periods)) = n_pre)) (PreH9 : ((Zlength (kinds)) = q_pre)) (PreH10 : ((Zlength (xs)) = q_pre)) (PreH11 : ((Zlength (ys)) = q_pre)) (PreH12 : ((Zlength (queries)) = q_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH14 : (PeriodsOK periods )) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH16 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH17 : (0 <= i)) (PreH18 : (i <= q_pre)) (PreH19 : (0 <= nout)) (PreH20 : (nout <= i)) (PreH21 : (nout = (AskCount (queries) (i)))) (PreH22 : ((Zlength (states)) = (i + 1 ))) (PreH23 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH24 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH25 : ((Zlength (arr)) = n_pre)) (PreH26 : (PeriodsOK arr )) (PreH27 : ((Zlength (answers)) = nout)) (PreH28 : (CellsShaped cells )) (PreH29 : (TreeOK cells arr 1 1 n_pre )) (PreH30 : (QueryStepsOK queries states i )) (PreH31 : (AnswersOK queries states answers i )) ,
  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (0 <= q_pre) ” 
  &&  “ ((Znth i kinds 0) <> 67) ” 
  &&  “ (i < q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ ((Zlength (kinds)) = q_pre) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6))) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0))))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (0 <= nout) ” 
  &&  “ (nout <= i) ” 
  &&  “ (nout = (AskCount (queries) (i))) ” 
  &&  “ ((Zlength (states)) = (i + 1 )) ” 
  &&  “ ((Znth (0) (states) ((@nil Z))) = periods) ” 
  &&  “ (arr = (Znth (i) (states) ((@nil Z)))) ” 
  &&  “ ((Zlength (arr)) = n_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ ((Zlength (answers)) = nout) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr 1 1 n_pre ) ” 
  &&  “ (QueryStepsOK queries states i ) ” 
  &&  “ (AnswersOK queries states answers i ) ”
  &&  (((qy_pre + (i * sizeof(INT)))) # Int  |-> (Znth i ys 0))
  **  (IntArray.missing_i qy_pre i 0 q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
.

Definition solver_partial_solve_wit_13_pure := 
(
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (0 <= q_pre)) (PreH2 : ((Znth i kinds 0) <> 67)) (PreH3 : (i < q_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 100000)) (PreH8 : ((Zlength (periods)) = n_pre)) (PreH9 : ((Zlength (kinds)) = q_pre)) (PreH10 : ((Zlength (xs)) = q_pre)) (PreH11 : ((Zlength (ys)) = q_pre)) (PreH12 : ((Zlength (queries)) = q_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH14 : (PeriodsOK periods )) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH16 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH17 : (0 <= i)) (PreH18 : (i <= q_pre)) (PreH19 : (0 <= nout)) (PreH20 : (nout <= i)) (PreH21 : (nout = (AskCount (queries) (i)))) (PreH22 : ((Zlength (states)) = (i + 1 ))) (PreH23 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH24 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH25 : ((Zlength (arr)) = n_pre)) (PreH26 : (PeriodsOK arr )) (PreH27 : ((Zlength (answers)) = nout)) (PreH28 : (CellsShaped cells )) (PreH29 : (TreeOK cells arr 1 1 n_pre )) (PreH30 : (QueryStepsOK queries states i )) (PreH31 : (AnswersOK queries states answers i )) ,
  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits 1 1 n_pre ) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (n_pre = (Zlength (arr))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= (Znth i xs 0)) ” 
  &&  “ ((Znth i xs 0) <= ((Znth i ys 0) - 1 )) ” 
  &&  “ (((Znth i ys 0) - 1 ) <= n_pre) ” 
  &&  “ (1 <= ((Znth i ys 0) - 1 )) ” 
  &&  “ ((Znth i xs 0) <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((0 + (2 * ((n_pre - 1 ) + 1 ) ) ) <= 400000) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr 1 1 n_pre ) ” 
  &&  “ ((0 + (2 * (((Zlength (periods)) - 1 ) + 1 ) ) ) <= 400000) ” 
  &&  “ ((Znth i xs 0) <= (Zlength (periods))) ” 
  &&  “ (((Znth i ys 0) - 1 ) <= (Zlength (periods))) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ (NodeFits 1 1 (Zlength (periods)) ) ”
) \/
(
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (nout <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (nout >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (0 <= q_pre)) (PreH10 : ((Znth i kinds 0) <> 67)) (PreH11 : (i < q_pre)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 100000)) (PreH16 : ((Zlength (periods)) = n_pre)) (PreH17 : ((Zlength (kinds)) = q_pre)) (PreH18 : ((Zlength (xs)) = q_pre)) (PreH19 : ((Zlength (ys)) = q_pre)) (PreH20 : ((Zlength (queries)) = q_pre)) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH22 : (PeriodsOK periods )) (PreH23 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH24 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH25 : (0 <= i)) (PreH26 : (i <= q_pre)) (PreH27 : (0 <= nout)) (PreH28 : (nout <= i)) (PreH29 : (nout = (AskCount (queries) (i)))) (PreH30 : ((Zlength (states)) = (i + 1 ))) (PreH31 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH32 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH33 : ((Zlength (arr)) = n_pre)) (PreH34 : (PeriodsOK arr )) (PreH35 : ((Zlength (answers)) = nout)) (PreH36 : (CellsShaped cells )) (PreH37 : (TreeOK cells arr 1 1 n_pre )) (PreH38 : (QueryStepsOK queries states i )) (PreH39 : (AnswersOK queries states answers i )) ,
  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits 1 1 n_pre ) ” 
  &&  “ (NodeFits 1 1 n_pre ) ”
).

Definition solver_partial_solve_wit_13_pure_split_goal_1 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (nout <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (nout >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (0 <= q_pre)) (PreH10 : ((Znth i kinds 0) <> 67)) (PreH11 : (i < q_pre)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 100000)) (PreH16 : ((Zlength (periods)) = n_pre)) (PreH17 : ((Zlength (kinds)) = q_pre)) (PreH18 : ((Zlength (xs)) = q_pre)) (PreH19 : ((Zlength (ys)) = q_pre)) (PreH20 : ((Zlength (queries)) = q_pre)) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH22 : (PeriodsOK periods )) (PreH23 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH24 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH25 : (0 <= i)) (PreH26 : (i <= q_pre)) (PreH27 : (0 <= nout)) (PreH28 : (nout <= i)) (PreH29 : (nout = (AskCount (queries) (i)))) (PreH30 : ((Zlength (states)) = (i + 1 ))) (PreH31 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH32 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH33 : ((Zlength (arr)) = n_pre)) (PreH34 : (PeriodsOK arr )) (PreH35 : ((Zlength (answers)) = nout)) (PreH36 : (CellsShaped cells )) (PreH37 : (TreeOK cells arr 1 1 n_pre )) (PreH38 : (QueryStepsOK queries states i )) (PreH39 : (AnswersOK queries states answers i )) ,
  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits 1 1 n_pre ) ”
.

Definition solver_partial_solve_wit_13_pure_split_goal_2 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (nout <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (q_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (nout >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (q_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (0 <= q_pre)) (PreH10 : ((Znth i kinds 0) <> 67)) (PreH11 : (i < q_pre)) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 100000)) (PreH16 : ((Zlength (periods)) = n_pre)) (PreH17 : ((Zlength (kinds)) = q_pre)) (PreH18 : ((Zlength (xs)) = q_pre)) (PreH19 : ((Zlength (ys)) = q_pre)) (PreH20 : ((Zlength (queries)) = q_pre)) (PreH21 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH22 : (PeriodsOK periods )) (PreH23 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH24 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH25 : (0 <= i)) (PreH26 : (i <= q_pre)) (PreH27 : (0 <= nout)) (PreH28 : (nout <= i)) (PreH29 : (nout = (AskCount (queries) (i)))) (PreH30 : ((Zlength (states)) = (i + 1 ))) (PreH31 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH32 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH33 : ((Zlength (arr)) = n_pre)) (PreH34 : (PeriodsOK arr )) (PreH35 : ((Zlength (answers)) = nout)) (PreH36 : (CellsShaped cells )) (PreH37 : (TreeOK cells arr 1 1 n_pre )) (PreH38 : (QueryStepsOK queries states i )) (PreH39 : (AnswersOK queries states answers i )) ,
  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "type" ) )) # Ptr  |-> type_pre)
  **  ((( &( "qx" ) )) # Ptr  |-> qx_pre)
  **  ((( &( "qy" ) )) # Ptr  |-> qy_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nout" ) )) # Int  |-> nout)
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits 1 1 n_pre ) ”
.

Definition solver_partial_solve_wit_13_aux := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (PreH1 : (0 <= q_pre)) (PreH2 : ((Znth i kinds 0) <> 67)) (PreH3 : (i < q_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 100000)) (PreH8 : ((Zlength (periods)) = n_pre)) (PreH9 : ((Zlength (kinds)) = q_pre)) (PreH10 : ((Zlength (xs)) = q_pre)) (PreH11 : ((Zlength (ys)) = q_pre)) (PreH12 : ((Zlength (queries)) = q_pre)) (PreH13 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH14 : (PeriodsOK periods )) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH16 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH17 : (0 <= i)) (PreH18 : (i <= q_pre)) (PreH19 : (0 <= nout)) (PreH20 : (nout <= i)) (PreH21 : (nout = (AskCount (queries) (i)))) (PreH22 : ((Zlength (states)) = (i + 1 ))) (PreH23 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH24 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH25 : ((Zlength (arr)) = n_pre)) (PreH26 : (PeriodsOK arr )) (PreH27 : ((Zlength (answers)) = nout)) (PreH28 : (CellsShaped cells )) (PreH29 : (TreeOK cells arr 1 1 n_pre )) (PreH30 : (QueryStepsOK queries states i )) (PreH31 : (AnswersOK queries states answers i )) ,
  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
|--
  “ (NodeFits 1 1 n_pre ) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (n_pre = (Zlength (arr))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= (Znth i xs 0)) ” 
  &&  “ ((Znth i xs 0) <= ((Znth i ys 0) - 1 )) ” 
  &&  “ (((Znth i ys 0) - 1 ) <= n_pre) ” 
  &&  “ (1 <= ((Znth i ys 0) - 1 )) ” 
  &&  “ ((Znth i xs 0) <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((0 + (2 * ((n_pre - 1 ) + 1 ) ) ) <= 400000) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr 1 1 n_pre ) ” 
  &&  “ ((0 + (2 * (((Zlength (periods)) - 1 ) + 1 ) ) ) <= 400000) ” 
  &&  “ ((Znth i xs 0) <= (Zlength (periods))) ” 
  &&  “ (((Znth i ys 0) - 1 ) <= (Zlength (periods))) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ (NodeFits 1 1 (Zlength (periods)) ) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ ((Znth i kinds 0) <> 67) ” 
  &&  “ (i < q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ ((Zlength (kinds)) = q_pre) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6))) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0))))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (0 <= nout) ” 
  &&  “ (nout <= i) ” 
  &&  “ (nout = (AskCount (queries) (i))) ” 
  &&  “ ((Zlength (states)) = (i + 1 )) ” 
  &&  “ ((Znth (0) (states) ((@nil Z))) = periods) ” 
  &&  “ (arr = (Znth (i) (states) ((@nil Z)))) ” 
  &&  “ ((Zlength (arr)) = n_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ ((Zlength (answers)) = nout) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr 1 1 n_pre ) ” 
  &&  “ (QueryStepsOK queries states i ) ” 
  &&  “ (AnswersOK queries states answers i ) ”
  &&  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
.

Definition solver_partial_solve_wit_13 := solver_partial_solve_wit_13_pure -> solver_partial_solve_wit_13_aux.

Definition solver_partial_solve_wit_14 := 
forall (out_pre: Z) (qy_pre: Z) (qx_pre: Z) (type_pre: Z) (q_pre: Z) (a_pre: Z) (n_pre: Z) (queries: (@list ((Z * Z) * Z))) (ys: (@list Z)) (xs: (@list Z)) (kinds: (@list Z)) (periods: (@list Z)) (cells: (@list (@list (@option Z)))) (answers: (@list Z)) (arr: (@list Z)) (states: (@list (@list Z))) (nout: Z) (i: Z) (retval: Z) (PreH1 : (retval = (cross ((QuerySlice (arr) (1) (n_pre) ((Znth i xs 0)) (((Znth i ys 0) - 1 )))) (0)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= (0 + (2 * ((n_pre - 1 ) + 1 ) ) ))) (PreH4 : (0 <= q_pre)) (PreH5 : ((Znth i kinds 0) <> 67)) (PreH6 : (i < q_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100000)) (PreH9 : (1 <= q_pre)) (PreH10 : (q_pre <= 100000)) (PreH11 : ((Zlength (periods)) = n_pre)) (PreH12 : ((Zlength (kinds)) = q_pre)) (PreH13 : ((Zlength (xs)) = q_pre)) (PreH14 : ((Zlength (ys)) = q_pre)) (PreH15 : ((Zlength (queries)) = q_pre)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6)))) (PreH17 : (PeriodsOK periods )) (PreH18 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0)))))) (PreH19 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6))))) (PreH20 : (0 <= i)) (PreH21 : (i <= q_pre)) (PreH22 : (0 <= nout)) (PreH23 : (nout <= i)) (PreH24 : (nout = (AskCount (queries) (i)))) (PreH25 : ((Zlength (states)) = (i + 1 ))) (PreH26 : ((Znth (0) (states) ((@nil Z))) = periods)) (PreH27 : (arr = (Znth (i) (states) ((@nil Z))))) (PreH28 : ((Zlength (arr)) = n_pre)) (PreH29 : (PeriodsOK arr )) (PreH30 : ((Zlength (answers)) = nout)) (PreH31 : (CellsShaped cells )) (PreH32 : (TreeOK cells arr 1 1 n_pre )) (PreH33 : (QueryStepsOK queries states i )) (PreH34 : (AnswersOK queries states answers i )) ,
  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
  **  (IntArray.undef_seg out_pre nout q_pre )
|--
  “ (retval = (cross ((QuerySlice (arr) (1) (n_pre) ((Znth i xs 0)) (((Znth i ys 0) - 1 )))) (0))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= (0 + (2 * ((n_pre - 1 ) + 1 ) ) )) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ ((Znth i kinds 0) <> 67) ” 
  &&  “ (i < q_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 100000) ” 
  &&  “ ((Zlength (periods)) = n_pre) ” 
  &&  “ ((Zlength (kinds)) = q_pre) ” 
  &&  “ ((Zlength (xs)) = q_pre) ” 
  &&  “ ((Zlength (ys)) = q_pre) ” 
  &&  “ ((Zlength (queries)) = q_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((2 <= (Znth j periods 0)) /\ ((Znth j periods 0) <= 6))) ” 
  &&  “ (PeriodsOK periods ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < q_pre)) -> ((Znth (j_2) (queries) ((pair ((pair (0) (0))) (0)))) = (pair ((pair ((Znth j_2 kinds 0)) ((Znth j_2 xs 0)))) ((Znth j_2 ys 0))))) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < q_pre)) -> ((((((Znth j_3 kinds 0) = 65) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) < (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= (n_pre + 1 ))) \/ ((((((Znth j_3 kinds 0) = 67) /\ (1 <= (Znth j_3 xs 0))) /\ ((Znth j_3 xs 0) <= n_pre)) /\ (2 <= (Znth j_3 ys 0))) /\ ((Znth j_3 ys 0) <= 6)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (0 <= nout) ” 
  &&  “ (nout <= i) ” 
  &&  “ (nout = (AskCount (queries) (i))) ” 
  &&  “ ((Zlength (states)) = (i + 1 )) ” 
  &&  “ ((Znth (0) (states) ((@nil Z))) = periods) ” 
  &&  “ (arr = (Znth (i) (states) ((@nil Z)))) ” 
  &&  “ ((Zlength (arr)) = n_pre) ” 
  &&  “ (PeriodsOK arr ) ” 
  &&  “ ((Zlength (answers)) = nout) ” 
  &&  “ (CellsShaped cells ) ” 
  &&  “ (TreeOK cells arr 1 1 n_pre ) ” 
  &&  “ (QueryStepsOK queries states i ) ” 
  &&  “ (AnswersOK queries states answers i ) ”
  &&  (((out_pre + (nout * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_pre (nout + 1 ) q_pre )
  **  (IntArray.seg ( &( "a_" ) ) 1 (n_pre + 1 ) arr )
  **  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells )
  **  (IntArray.full qy_pre q_pre ys )
  **  (IntArray.full qx_pre q_pre xs )
  **  (CharArray.full type_pre q_pre kinds )
  **  (IntArray.seg a_pre 1 (n_pre + 1 ) periods )
  **  (IntArray.full out_pre nout answers )
.

Definition solver_which_implies_wit_1 := 
(
  (IntArray2.undef_full ( &( "seg" ) ) 400020 60 )
|--
  EX (cells0: (@list (@list (@option Z)))) ,
  “ (CellsShaped cells0 ) ”
  &&  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0 )
) \/
(
  (IntArray2.undef_full ( &( "seg" ) ) 400020 60 )
|--
  EX (cells0: (@list (@list (@option Z)))) ,
  “ (CellsShaped cells0 ) ”
  &&  (IntArray2.mixed_full ( &( "seg" ) ) 400020 60 cells0 )
).

Module Type VC_Correct.

Include array2_Strategy_Correct.
Include array2_char_Strategy_Correct.
Include int_array_Strategy_Correct.
Include char_array_Strategy_Correct.
Include array2_ext_Strategy_Correct.

Axiom proof_of_pull_safety_wit_1 : pull_safety_wit_1.
Axiom proof_of_pull_safety_wit_2 : pull_safety_wit_2.
Axiom proof_of_pull_safety_wit_3 : pull_safety_wit_3.
Axiom proof_of_pull_safety_wit_4 : pull_safety_wit_4.
Axiom proof_of_pull_safety_wit_5 : pull_safety_wit_5.
Axiom proof_of_pull_safety_wit_6 : pull_safety_wit_6.
Axiom proof_of_pull_safety_wit_7 : pull_safety_wit_7.
Axiom proof_of_pull_safety_wit_8 : pull_safety_wit_8.
Axiom proof_of_pull_safety_wit_9 : pull_safety_wit_9.
Axiom proof_of_pull_safety_wit_10 : pull_safety_wit_10.
Axiom proof_of_pull_safety_wit_11 : pull_safety_wit_11.
Axiom proof_of_pull_safety_wit_12 : pull_safety_wit_12.
Axiom proof_of_pull_safety_wit_13 : pull_safety_wit_13.
Axiom proof_of_pull_entail_wit_1 : pull_entail_wit_1.
Axiom proof_of_pull_entail_wit_2 : pull_entail_wit_2.
Axiom proof_of_pull_entail_wit_3 : pull_entail_wit_3.
Axiom proof_of_pull_return_wit_1 : pull_return_wit_1.
Axiom proof_of_pull_partial_solve_wit_1_pure : pull_partial_solve_wit_1_pure.
Axiom proof_of_pull_partial_solve_wit_1 : pull_partial_solve_wit_1.
Axiom proof_of_pull_partial_solve_wit_2_pure : pull_partial_solve_wit_2_pure.
Axiom proof_of_pull_partial_solve_wit_2 : pull_partial_solve_wit_2.
Axiom proof_of_pull_partial_solve_wit_3 : pull_partial_solve_wit_3.
Axiom proof_of_build_safety_wit_1 : build_safety_wit_1.
Axiom proof_of_build_safety_wit_2 : build_safety_wit_2.
Axiom proof_of_build_safety_wit_3 : build_safety_wit_3.
Axiom proof_of_build_safety_wit_4 : build_safety_wit_4.
Axiom proof_of_build_safety_wit_5 : build_safety_wit_5.
Axiom proof_of_build_safety_wit_6 : build_safety_wit_6.
Axiom proof_of_build_safety_wit_7 : build_safety_wit_7.
Axiom proof_of_build_safety_wit_8 : build_safety_wit_8.
Axiom proof_of_build_safety_wit_9 : build_safety_wit_9.
Axiom proof_of_build_safety_wit_10 : build_safety_wit_10.
Axiom proof_of_build_safety_wit_11 : build_safety_wit_11.
Axiom proof_of_build_safety_wit_12 : build_safety_wit_12.
Axiom proof_of_build_safety_wit_13 : build_safety_wit_13.
Axiom proof_of_build_safety_wit_14 : build_safety_wit_14.
Axiom proof_of_build_safety_wit_15 : build_safety_wit_15.
Axiom proof_of_build_safety_wit_16 : build_safety_wit_16.
Axiom proof_of_build_safety_wit_17 : build_safety_wit_17.
Axiom proof_of_build_safety_wit_18 : build_safety_wit_18.
Axiom proof_of_build_safety_wit_19 : build_safety_wit_19.
Axiom proof_of_build_entail_wit_1 : build_entail_wit_1.
Axiom proof_of_build_entail_wit_2_1 : build_entail_wit_2_1.
Axiom proof_of_build_entail_wit_2_2 : build_entail_wit_2_2.
Axiom proof_of_build_entail_wit_3 : build_entail_wit_3.
Axiom proof_of_build_return_wit_1 : build_return_wit_1.
Axiom proof_of_build_return_wit_2 : build_return_wit_2.
Axiom proof_of_build_partial_solve_wit_1 : build_partial_solve_wit_1.
Axiom proof_of_build_partial_solve_wit_2 : build_partial_solve_wit_2.
Axiom proof_of_build_partial_solve_wit_3 : build_partial_solve_wit_3.
Axiom proof_of_build_partial_solve_wit_4_pure : build_partial_solve_wit_4_pure.
Axiom proof_of_build_partial_solve_wit_4 : build_partial_solve_wit_4.
Axiom proof_of_build_partial_solve_wit_5_pure : build_partial_solve_wit_5_pure.
Axiom proof_of_build_partial_solve_wit_5 : build_partial_solve_wit_5.
Axiom proof_of_build_partial_solve_wit_6_pure : build_partial_solve_wit_6_pure.
Axiom proof_of_build_partial_solve_wit_6 : build_partial_solve_wit_6.
Axiom proof_of_update_safety_wit_1 : update_safety_wit_1.
Axiom proof_of_update_safety_wit_2 : update_safety_wit_2.
Axiom proof_of_update_safety_wit_3 : update_safety_wit_3.
Axiom proof_of_update_safety_wit_4 : update_safety_wit_4.
Axiom proof_of_update_safety_wit_5 : update_safety_wit_5.
Axiom proof_of_update_safety_wit_6 : update_safety_wit_6.
Axiom proof_of_update_safety_wit_7 : update_safety_wit_7.
Axiom proof_of_update_safety_wit_8 : update_safety_wit_8.
Axiom proof_of_update_safety_wit_9 : update_safety_wit_9.
Axiom proof_of_update_safety_wit_10 : update_safety_wit_10.
Axiom proof_of_update_safety_wit_11 : update_safety_wit_11.
Axiom proof_of_update_safety_wit_12 : update_safety_wit_12.
Axiom proof_of_update_safety_wit_13 : update_safety_wit_13.
Axiom proof_of_update_safety_wit_14 : update_safety_wit_14.
Axiom proof_of_update_safety_wit_15 : update_safety_wit_15.
Axiom proof_of_update_safety_wit_16 : update_safety_wit_16.
Axiom proof_of_update_safety_wit_17 : update_safety_wit_17.
Axiom proof_of_update_safety_wit_18 : update_safety_wit_18.
Axiom proof_of_update_safety_wit_19 : update_safety_wit_19.
Axiom proof_of_update_entail_wit_1 : update_entail_wit_1.
Axiom proof_of_update_entail_wit_2_1 : update_entail_wit_2_1.
Axiom proof_of_update_entail_wit_2_2 : update_entail_wit_2_2.
Axiom proof_of_update_entail_wit_3_1 : update_entail_wit_3_1.
Axiom proof_of_update_entail_wit_3_2 : update_entail_wit_3_2.
Axiom proof_of_update_return_wit_1 : update_return_wit_1.
Axiom proof_of_update_return_wit_2 : update_return_wit_2.
Axiom proof_of_update_partial_solve_wit_1 : update_partial_solve_wit_1.
Axiom proof_of_update_partial_solve_wit_2 : update_partial_solve_wit_2.
Axiom proof_of_update_partial_solve_wit_3 : update_partial_solve_wit_3.
Axiom proof_of_update_partial_solve_wit_4_pure : update_partial_solve_wit_4_pure.
Axiom proof_of_update_partial_solve_wit_4 : update_partial_solve_wit_4.
Axiom proof_of_update_partial_solve_wit_5_pure : update_partial_solve_wit_5_pure.
Axiom proof_of_update_partial_solve_wit_5 : update_partial_solve_wit_5.
Axiom proof_of_update_partial_solve_wit_6_pure : update_partial_solve_wit_6_pure.
Axiom proof_of_update_partial_solve_wit_6 : update_partial_solve_wit_6.
Axiom proof_of_query_safety_wit_1 : query_safety_wit_1.
Axiom proof_of_query_safety_wit_2 : query_safety_wit_2.
Axiom proof_of_query_safety_wit_3 : query_safety_wit_3.
Axiom proof_of_query_safety_wit_4 : query_safety_wit_4.
Axiom proof_of_query_safety_wit_5 : query_safety_wit_5.
Axiom proof_of_query_safety_wit_6 : query_safety_wit_6.
Axiom proof_of_query_safety_wit_7 : query_safety_wit_7.
Axiom proof_of_query_safety_wit_8 : query_safety_wit_8.
Axiom proof_of_query_safety_wit_9 : query_safety_wit_9.
Axiom proof_of_query_safety_wit_10 : query_safety_wit_10.
Axiom proof_of_query_safety_wit_11 : query_safety_wit_11.
Axiom proof_of_query_safety_wit_12 : query_safety_wit_12.
Axiom proof_of_query_safety_wit_13 : query_safety_wit_13.
Axiom proof_of_query_safety_wit_14 : query_safety_wit_14.
Axiom proof_of_query_safety_wit_15 : query_safety_wit_15.
Axiom proof_of_query_safety_wit_16 : query_safety_wit_16.
Axiom proof_of_query_safety_wit_17 : query_safety_wit_17.
Axiom proof_of_query_safety_wit_18 : query_safety_wit_18.
Axiom proof_of_query_safety_wit_19 : query_safety_wit_19.
Axiom proof_of_query_safety_wit_20 : query_safety_wit_20.
Axiom proof_of_query_safety_wit_21 : query_safety_wit_21.
Axiom proof_of_query_safety_wit_22 : query_safety_wit_22.
Axiom proof_of_query_safety_wit_23 : query_safety_wit_23.
Axiom proof_of_query_safety_wit_24 : query_safety_wit_24.
Axiom proof_of_query_safety_wit_25 : query_safety_wit_25.
Axiom proof_of_query_safety_wit_26 : query_safety_wit_26.
Axiom proof_of_query_safety_wit_27 : query_safety_wit_27.
Axiom proof_of_query_safety_wit_28 : query_safety_wit_28.
Axiom proof_of_query_safety_wit_29 : query_safety_wit_29.
Axiom proof_of_query_safety_wit_30 : query_safety_wit_30.
Axiom proof_of_query_safety_wit_31 : query_safety_wit_31.
Axiom proof_of_query_safety_wit_32 : query_safety_wit_32.
Axiom proof_of_query_safety_wit_33 : query_safety_wit_33.
Axiom proof_of_query_safety_wit_34 : query_safety_wit_34.
Axiom proof_of_query_safety_wit_35 : query_safety_wit_35.
Axiom proof_of_query_safety_wit_36 : query_safety_wit_36.
Axiom proof_of_query_safety_wit_37 : query_safety_wit_37.
Axiom proof_of_query_safety_wit_38 : query_safety_wit_38.
Axiom proof_of_query_safety_wit_39 : query_safety_wit_39.
Axiom proof_of_query_safety_wit_40 : query_safety_wit_40.
Axiom proof_of_query_safety_wit_41 : query_safety_wit_41.
Axiom proof_of_query_entail_wit_1 : query_entail_wit_1.
Axiom proof_of_query_return_wit_1 : query_return_wit_1.
Axiom proof_of_query_return_wit_2 : query_return_wit_2.
Axiom proof_of_query_return_wit_3 : query_return_wit_3.
Axiom proof_of_query_return_wit_4 : query_return_wit_4.
Axiom proof_of_query_return_wit_5 : query_return_wit_5.
Axiom proof_of_query_return_wit_6 : query_return_wit_6.
Axiom proof_of_query_return_wit_7 : query_return_wit_7.
Axiom proof_of_query_partial_solve_wit_1_pure : query_partial_solve_wit_1_pure.
Axiom proof_of_query_partial_solve_wit_1 : query_partial_solve_wit_1.
Axiom proof_of_query_partial_solve_wit_2_pure : query_partial_solve_wit_2_pure.
Axiom proof_of_query_partial_solve_wit_2 : query_partial_solve_wit_2.
Axiom proof_of_query_partial_solve_wit_3_pure : query_partial_solve_wit_3_pure.
Axiom proof_of_query_partial_solve_wit_3 : query_partial_solve_wit_3.
Axiom proof_of_query_partial_solve_wit_4_pure : query_partial_solve_wit_4_pure.
Axiom proof_of_query_partial_solve_wit_4 : query_partial_solve_wit_4.
Axiom proof_of_query_partial_solve_wit_5_pure : query_partial_solve_wit_5_pure.
Axiom proof_of_query_partial_solve_wit_5 : query_partial_solve_wit_5.
Axiom proof_of_query_partial_solve_wit_6_pure : query_partial_solve_wit_6_pure.
Axiom proof_of_query_partial_solve_wit_6 : query_partial_solve_wit_6.
Axiom proof_of_query_partial_solve_wit_7_pure : query_partial_solve_wit_7_pure.
Axiom proof_of_query_partial_solve_wit_7 : query_partial_solve_wit_7.
Axiom proof_of_query_partial_solve_wit_8_pure : query_partial_solve_wit_8_pure.
Axiom proof_of_query_partial_solve_wit_8 : query_partial_solve_wit_8.
Axiom proof_of_query_partial_solve_wit_9_pure : query_partial_solve_wit_9_pure.
Axiom proof_of_query_partial_solve_wit_9 : query_partial_solve_wit_9.
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10_pure : solver_partial_solve_wit_10_pure.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.
Axiom proof_of_solver_partial_solve_wit_13_pure : solver_partial_solve_wit_13_pure.
Axiom proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13.
Axiom proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14.
Axiom proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.

End VC_Correct.
