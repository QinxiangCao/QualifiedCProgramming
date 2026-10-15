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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P011_765A_neverending_competitions_lib.
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
forall (n_pre: Z) (flights_pre: Z) (home_pre: Z) (flight_rows: (@list (@list (@option Z)))) (flights_data: (@list ((@list Z) * (@list Z)))) (home_data: (@list Z))  __default__Prod__List_Z__List_Z (PreH1 : ((Zlength (home_data)) = 3)) (PreH2 : forall (j: Z) , (((0 <= j) /\ (j < 3)) -> ((65 <= (Znth j home_data 0)) /\ ((Znth j home_data 0) <= 90)))) (PreH3 : (1 <= (Zlength (flights_data)))) (PreH4 : ((Zlength (flights_data)) <= 100)) (PreH5 : (Pre home_data flights_data )) (PreH6 : (n_pre = (Zlength (flights_data)))) (PreH7 : ((Zlength (flight_rows)) = n_pre)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((((((((Zlength ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3) /\ ((Zlength ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3)) /\ ((Zlength ((Znth (i) (flight_rows) ((@nil (@option Z)))))) = 16)) /\ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < 3)) -> ((((((65 <= (Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0))) /\ ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)) <= 90)) /\ (65 <= (Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))) /\ ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)) <= 90)) /\ ((Znth (j_2) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))))) /\ ((Znth ((5 + j_2 )) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))))))) /\ ((Znth (3) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (45)))) /\ ((Znth (4) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (62)))) /\ ((Znth (8) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  ((( &( "home" ) )) # Ptr  |-> home_pre)
  **  ((( &( "flights" ) )) # Ptr  |-> flights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string home_pre home_data )
  **  (CharArray2.mixed_full flights_pre n_pre 16 flight_rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_2 := 
forall (n_pre: Z) (flights_pre: Z) (home_pre: Z) (flight_rows: (@list (@list (@option Z)))) (flights_data: (@list ((@list Z) * (@list Z)))) (home_data: (@list Z))  __default__Prod__List_Z__List_Z (PreH1 : ((Zlength (home_data)) = 3)) (PreH2 : forall (j: Z) , (((0 <= j) /\ (j < 3)) -> ((65 <= (Znth j home_data 0)) /\ ((Znth j home_data 0) <= 90)))) (PreH3 : (1 <= (Zlength (flights_data)))) (PreH4 : ((Zlength (flights_data)) <= 100)) (PreH5 : (Pre home_data flights_data )) (PreH6 : (n_pre = (Zlength (flights_data)))) (PreH7 : ((Zlength (flight_rows)) = n_pre)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((((((((Zlength ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3) /\ ((Zlength ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3)) /\ ((Zlength ((Znth (i) (flight_rows) ((@nil (@option Z)))))) = 16)) /\ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < 3)) -> ((((((65 <= (Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0))) /\ ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)) <= 90)) /\ (65 <= (Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))) /\ ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)) <= 90)) /\ ((Znth (j_2) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))))) /\ ((Znth ((5 + j_2 )) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))))))) /\ ((Znth (3) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (45)))) /\ ((Znth (4) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (62)))) /\ ((Znth (8) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  ((( &( "home" ) )) # Ptr  |-> home_pre)
  **  ((( &( "flights" ) )) # Ptr  |-> flights_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string home_pre home_data )
  **  (CharArray2.mixed_full flights_pre n_pre 16 flight_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_return_wit_1 := 
(
forall (n_pre: Z) (flights_pre: Z) (home_pre: Z) (flight_rows: (@list (@list (@option Z)))) (flights_data: (@list ((@list Z) * (@list Z)))) (home_data: (@list Z))  __default__Prod__List_Z__List_Z (PreH1 : ((Z.land n_pre 1) <> 0)) (PreH2 : ((Zlength (home_data)) = 3)) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < 3)) -> ((65 <= (Znth j home_data 0)) /\ ((Znth j home_data 0) <= 90)))) (PreH4 : (1 <= (Zlength (flights_data)))) (PreH5 : ((Zlength (flights_data)) <= 100)) (PreH6 : (Pre home_data flights_data )) (PreH7 : (n_pre = (Zlength (flights_data)))) (PreH8 : ((Zlength (flight_rows)) = n_pre)) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((((((((Zlength ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3) /\ ((Zlength ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3)) /\ ((Zlength ((Znth (i) (flight_rows) ((@nil (@option Z)))))) = 16)) /\ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < 3)) -> ((((((65 <= (Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0))) /\ ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)) <= 90)) /\ (65 <= (Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))) /\ ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)) <= 90)) /\ ((Znth (j_2) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))))) /\ ((Znth ((5 + j_2 )) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))))))) /\ ((Znth (3) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (45)))) /\ ((Znth (4) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (62)))) /\ ((Znth (8) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (store_string home_pre home_data )
  **  (CharArray2.mixed_full flights_pre n_pre 16 flight_rows )
|--
  EX (result: (@list Z)) ,
  “ (Spec home_data flights_data result ) ” 
  &&  “ (0 = 0) ” 
  &&  “ (result = (cons (99) ((cons (111) ((cons (110) ((cons (116) ((cons (101) ((cons (115) ((cons (116) ((@nil Z)))))))))))))))) ”
  &&  (store_string home_pre home_data )
  **  (CharArray2.mixed_full flights_pre n_pre 16 flight_rows )
) \/
(
forall (n_pre: Z) (flight_rows: (@list (@list (@option Z)))) (flights_data: (@list ((@list Z) * (@list Z)))) (home_data: (@list Z))  __default__Prod__List_Z__List_Z (PreH1 : ((Z.land n_pre 1) <> 0)) (PreH2 : ((Zlength (home_data)) = 3)) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < 3)) -> ((65 <= (Znth j home_data 0)) /\ ((Znth j home_data 0) <= 90)))) (PreH4 : (1 <= (Zlength (flights_data)))) (PreH5 : ((Zlength (flights_data)) <= 100)) (PreH6 : (Pre home_data flights_data )) (PreH7 : (n_pre = (Zlength (flights_data)))) (PreH8 : ((Zlength (flight_rows)) = n_pre)) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((((((((Zlength ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3) /\ ((Zlength ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3)) /\ ((Zlength ((Znth (i) (flight_rows) ((@nil (@option Z)))))) = 16)) /\ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < 3)) -> ((((((65 <= (Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0))) /\ ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)) <= 90)) /\ (65 <= (Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))) /\ ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)) <= 90)) /\ ((Znth (j_2) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))))) /\ ((Znth ((5 + j_2 )) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))))))) /\ ((Znth (3) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (45)))) /\ ((Znth (4) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (62)))) /\ ((Znth (8) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  TT && emp 
|--
  “ (Spec home_data flights_data (cons (99) ((cons (111) ((cons (110) ((cons (116) ((cons (101) ((cons (115) ((cons (116) ((@nil Z))))))))))))))) ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (flight_rows: (@list (@list (@option Z)))) (flights_data: (@list ((@list Z) * (@list Z)))) (home_data: (@list Z))  __default__Prod__List_Z__List_Z (PreH1 : ((Z.land n_pre 1) <> 0)) (PreH2 : ((Zlength (home_data)) = 3)) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < 3)) -> ((65 <= (Znth j home_data 0)) /\ ((Znth j home_data 0) <= 90)))) (PreH4 : (1 <= (Zlength (flights_data)))) (PreH5 : ((Zlength (flights_data)) <= 100)) (PreH6 : (Pre home_data flights_data )) (PreH7 : (n_pre = (Zlength (flights_data)))) (PreH8 : ((Zlength (flight_rows)) = n_pre)) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((((((((Zlength ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3) /\ ((Zlength ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3)) /\ ((Zlength ((Znth (i) (flight_rows) ((@nil (@option Z)))))) = 16)) /\ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < 3)) -> ((((((65 <= (Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0))) /\ ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)) <= 90)) /\ (65 <= (Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))) /\ ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)) <= 90)) /\ ((Znth (j_2) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))))) /\ ((Znth ((5 + j_2 )) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))))))) /\ ((Znth (3) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (45)))) /\ ((Znth (4) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (62)))) /\ ((Znth (8) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (Spec home_data flights_data (cons (99) ((cons (111) ((cons (110) ((cons (116) ((cons (101) ((cons (115) ((cons (116) ((@nil Z))))))))))))))) )
.

Definition solver_return_wit_2 := 
(
forall (n_pre: Z) (flights_pre: Z) (home_pre: Z) (flight_rows: (@list (@list (@option Z)))) (flights_data: (@list ((@list Z) * (@list Z)))) (home_data: (@list Z))  __default__Prod__List_Z__List_Z (PreH1 : ((Z.land n_pre 1) = 0)) (PreH2 : ((Zlength (home_data)) = 3)) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < 3)) -> ((65 <= (Znth j home_data 0)) /\ ((Znth j home_data 0) <= 90)))) (PreH4 : (1 <= (Zlength (flights_data)))) (PreH5 : ((Zlength (flights_data)) <= 100)) (PreH6 : (Pre home_data flights_data )) (PreH7 : (n_pre = (Zlength (flights_data)))) (PreH8 : ((Zlength (flight_rows)) = n_pre)) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((((((((Zlength ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3) /\ ((Zlength ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3)) /\ ((Zlength ((Znth (i) (flight_rows) ((@nil (@option Z)))))) = 16)) /\ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < 3)) -> ((((((65 <= (Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0))) /\ ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)) <= 90)) /\ (65 <= (Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))) /\ ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)) <= 90)) /\ ((Znth (j_2) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))))) /\ ((Znth ((5 + j_2 )) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))))))) /\ ((Znth (3) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (45)))) /\ ((Znth (4) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (62)))) /\ ((Znth (8) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (store_string home_pre home_data )
  **  (CharArray2.mixed_full flights_pre n_pre 16 flight_rows )
|--
  EX (result: (@list Z)) ,
  “ (Spec home_data flights_data result ) ” 
  &&  “ (1 = 1) ” 
  &&  “ (result = (cons (104) ((cons (111) ((cons (109) ((cons (101) ((@nil Z)))))))))) ”
  &&  (store_string home_pre home_data )
  **  (CharArray2.mixed_full flights_pre n_pre 16 flight_rows )
) \/
(
forall (n_pre: Z) (flight_rows: (@list (@list (@option Z)))) (flights_data: (@list ((@list Z) * (@list Z)))) (home_data: (@list Z))  __default__Prod__List_Z__List_Z (PreH1 : ((Z.land n_pre 1) = 0)) (PreH2 : ((Zlength (home_data)) = 3)) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < 3)) -> ((65 <= (Znth j home_data 0)) /\ ((Znth j home_data 0) <= 90)))) (PreH4 : (1 <= (Zlength (flights_data)))) (PreH5 : ((Zlength (flights_data)) <= 100)) (PreH6 : (Pre home_data flights_data )) (PreH7 : (n_pre = (Zlength (flights_data)))) (PreH8 : ((Zlength (flight_rows)) = n_pre)) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((((((((Zlength ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3) /\ ((Zlength ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3)) /\ ((Zlength ((Znth (i) (flight_rows) ((@nil (@option Z)))))) = 16)) /\ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < 3)) -> ((((((65 <= (Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0))) /\ ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)) <= 90)) /\ (65 <= (Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))) /\ ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)) <= 90)) /\ ((Znth (j_2) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))))) /\ ((Znth ((5 + j_2 )) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))))))) /\ ((Znth (3) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (45)))) /\ ((Znth (4) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (62)))) /\ ((Znth (8) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  TT && emp 
|--
  “ (Spec home_data flights_data (cons (104) ((cons (111) ((cons (109) ((cons (101) ((@nil Z))))))))) ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (flight_rows: (@list (@list (@option Z)))) (flights_data: (@list ((@list Z) * (@list Z)))) (home_data: (@list Z))  __default__Prod__List_Z__List_Z (PreH1 : ((Z.land n_pre 1) = 0)) (PreH2 : ((Zlength (home_data)) = 3)) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < 3)) -> ((65 <= (Znth j home_data 0)) /\ ((Znth j home_data 0) <= 90)))) (PreH4 : (1 <= (Zlength (flights_data)))) (PreH5 : ((Zlength (flights_data)) <= 100)) (PreH6 : (Pre home_data flights_data )) (PreH7 : (n_pre = (Zlength (flights_data)))) (PreH8 : ((Zlength (flight_rows)) = n_pre)) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((((((((Zlength ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3) /\ ((Zlength ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3)) /\ ((Zlength ((Znth (i) (flight_rows) ((@nil (@option Z)))))) = 16)) /\ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < 3)) -> ((((((65 <= (Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0))) /\ ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)) <= 90)) /\ (65 <= (Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))) /\ ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)) <= 90)) /\ ((Znth (j_2) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))))) /\ ((Znth ((5 + j_2 )) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) (0)))))))) /\ ((Znth (3) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (45)))) /\ ((Znth (4) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (62)))) /\ ((Znth (8) ((Znth (i) (flight_rows) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (Spec home_data flights_data (cons (104) ((cons (111) ((cons (109) ((cons (101) ((@nil Z))))))))) )
.

Module Type VC_Correct.

Include array2_Strategy_Correct.
Include array2_char_Strategy_Correct.
Include int_array_Strategy_Correct.
Include char_array_Strategy_Correct.
Include array2_ext_Strategy_Correct.

Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.

End VC_Correct.
