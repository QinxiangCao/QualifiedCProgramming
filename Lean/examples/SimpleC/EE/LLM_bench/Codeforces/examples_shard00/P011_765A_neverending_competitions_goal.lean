import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P011_765A_neverending_competitions_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P011_765A_neverending_competitions_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P011_765A_neverending_competitions_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P011_765A_neverending_competitions_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev charArray2 := naive_C_Rules.CharArray2
private noncomputable abbrev charArray3 := naive_C_Rules.CharArray3
private noncomputable abbrev charPtrArray2 := naive_C_Rules.CharPtrArray2
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev ucharArray2 := naive_C_Rules.UCharArray2
private noncomputable abbrev ucharArray3 := naive_C_Rules.UCharArray3
private noncomputable abbrev ucharPtrArray2 := naive_C_Rules.UCharPtrArray2
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev shortArray2 := naive_C_Rules.ShortArray2
private noncomputable abbrev shortArray3 := naive_C_Rules.ShortArray3
private noncomputable abbrev shortPtrArray2 := naive_C_Rules.ShortPtrArray2
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev ushortArray2 := naive_C_Rules.UShortArray2
private noncomputable abbrev ushortArray3 := naive_C_Rules.UShortArray3
private noncomputable abbrev ushortPtrArray2 := naive_C_Rules.UShortPtrArray2
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev intArray2 := naive_C_Rules.IntArray2
private noncomputable abbrev intArray3 := naive_C_Rules.IntArray3
private noncomputable abbrev intPtrArray2 := naive_C_Rules.IntPtrArray2
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev uintArray2 := naive_C_Rules.UIntArray2
private noncomputable abbrev uintArray3 := naive_C_Rules.UIntArray3
private noncomputable abbrev uintPtrArray2 := naive_C_Rules.UIntPtrArray2
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev int64Array2 := naive_C_Rules.Int64Array2
private noncomputable abbrev int64Array3 := naive_C_Rules.Int64Array3
private noncomputable abbrev int64PtrArray2 := naive_C_Rules.Int64PtrArray2
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev uint64Array2 := naive_C_Rules.UInt64Array2
private noncomputable abbrev uint64Array3 := naive_C_Rules.UInt64Array3
private noncomputable abbrev uint64PtrArray2 := naive_C_Rules.UInt64PtrArray2
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray
private noncomputable abbrev ptrArray2 := naive_C_Rules.PtrArray2
private noncomputable abbrev ptrArray3 := naive_C_Rules.PtrArray3
private noncomputable abbrev ptrPtrArray2 := naive_C_Rules.PtrPtrArray2
private noncomputable abbrev store_string := naive_C_Rules.store_string

noncomputable def solver_safety_wit_1 : Prop :=
  forall (flight_rows : (List (List (Option Int)))) (flights_data : (List ((List Int) × (List Int)))) (home_data : (List Int)) (home_pre : Int) (flights_pre : Int) (n_pre : Int) (__default__Prod__List_Z__List_Z : _Prod__List_Z__List_Z) (PreH1 : ((Zlength (home_data)) = 3)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < 3)) -> ((65 <= (Znth j home_data (0 : Int))) ∧ ((Znth j home_data (0 : Int)) <= 90)))) (PreH3 : (1 <= (Zlength (flights_data)))) (PreH4 : ((Zlength (flights_data)) <= 100)) (PreH5 : (Pre home_data flights_data)) (PreH6 : (n_pre = (Zlength (flights_data)))) (PreH7 : ((Zlength (flight_rows)) = n_pre)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((((((Zlength ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3) ∧ ((Zlength ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3)) ∧ ((Zlength ((Znth (i) (flight_rows) ((@List.nil (Option Int)))))) = 16)) ∧ forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < 3)) -> ((((((65 <= (Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int)))) ∧ ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))) <= 90)) ∧ (65 <= (Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))) ∧ ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))) <= 90)) ∧ ((Znth (j_2) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))))) ∧ ((Znth ((5 + j_2)) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))))))) ∧ ((Znth (3) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some (45)))) ∧ ((Znth (4) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some (62)))) ∧ ((Znth (8) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((0 : Int))))))) ,
  ((( &( "home" ) )) # Ptr |-> (home_pre))
  ** ((( &( "flights" ) )) # Ptr |-> (flights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (store_string home_pre home_data)
  ** (charArray2.mixed_full flights_pre n_pre 16 flight_rows)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (flight_rows : (List (List (Option Int)))) (flights_data : (List ((List Int) × (List Int)))) (home_data : (List Int)) (home_pre : Int) (flights_pre : Int) (n_pre : Int) (__default__Prod__List_Z__List_Z : _Prod__List_Z__List_Z) (PreH1 : ((Zlength (home_data)) = 3)) (PreH2 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < 3)) -> ((65 <= (Znth j home_data (0 : Int))) ∧ ((Znth j home_data (0 : Int)) <= 90)))) (PreH3 : (1 <= (Zlength (flights_data)))) (PreH4 : ((Zlength (flights_data)) <= 100)) (PreH5 : (Pre home_data flights_data)) (PreH6 : (n_pre = (Zlength (flights_data)))) (PreH7 : ((Zlength (flight_rows)) = n_pre)) (PreH8 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((((((Zlength ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3) ∧ ((Zlength ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3)) ∧ ((Zlength ((Znth (i) (flight_rows) ((@List.nil (Option Int)))))) = 16)) ∧ forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < 3)) -> ((((((65 <= (Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int)))) ∧ ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))) <= 90)) ∧ (65 <= (Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))) ∧ ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))) <= 90)) ∧ ((Znth (j_2) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))))) ∧ ((Znth ((5 + j_2)) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))))))) ∧ ((Znth (3) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some (45)))) ∧ ((Znth (4) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some (62)))) ∧ ((Znth (8) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((0 : Int))))))) ,
  ((( &( "home" ) )) # Ptr |-> (home_pre))
  ** ((( &( "flights" ) )) # Ptr |-> (flights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (store_string home_pre home_data)
  ** (charArray2.mixed_full flights_pre n_pre 16 flight_rows)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (flight_rows : (List (List (Option Int)))) (flights_data : (List ((List Int) × (List Int)))) (home_data : (List Int)) (home_pre : Int) (flights_pre : Int) (n_pre : Int) (__default__Prod__List_Z__List_Z : _Prod__List_Z__List_Z) (PreH1 : ((Z.land n_pre 1) ≠ (0 : Int))) (PreH2 : ((Zlength (home_data)) = 3)) (PreH3 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < 3)) -> ((65 <= (Znth j home_data (0 : Int))) ∧ ((Znth j home_data (0 : Int)) <= 90)))) (PreH4 : (1 <= (Zlength (flights_data)))) (PreH5 : ((Zlength (flights_data)) <= 100)) (PreH6 : (Pre home_data flights_data)) (PreH7 : (n_pre = (Zlength (flights_data)))) (PreH8 : ((Zlength (flight_rows)) = n_pre)) (PreH9 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((((((Zlength ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3) ∧ ((Zlength ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3)) ∧ ((Zlength ((Znth (i) (flight_rows) ((@List.nil (Option Int)))))) = 16)) ∧ forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < 3)) -> ((((((65 <= (Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int)))) ∧ ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))) <= 90)) ∧ (65 <= (Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))) ∧ ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))) <= 90)) ∧ ((Znth (j_2) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))))) ∧ ((Znth ((5 + j_2)) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))))))) ∧ ((Znth (3) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some (45)))) ∧ ((Znth (4) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some (62)))) ∧ ((Znth (8) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((0 : Int))))))) ,
  (store_string home_pre home_data)
  ** (charArray2.mixed_full flights_pre n_pre 16 flight_rows)
|--
  EX result : (List Int),
  “ (Spec home_data flights_data result) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (result = (99 :: (111 :: (110 :: (116 :: (101 :: (115 :: (116 :: (@List.nil Int))))))))) ”
  &&  (store_string home_pre home_data)
  ** (charArray2.mixed_full flights_pre n_pre 16 flight_rows)
) \/
(
forall (flight_rows : (List (List (Option Int)))) (flights_data : (List ((List Int) × (List Int)))) (home_data : (List Int)) (n_pre : Int) (__default__Prod__List_Z__List_Z : _Prod__List_Z__List_Z) (PreH1 : ((Z.land n_pre 1) ≠ (0 : Int))) (PreH2 : ((Zlength (home_data)) = 3)) (PreH3 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < 3)) -> ((65 <= (Znth j home_data (0 : Int))) ∧ ((Znth j home_data (0 : Int)) <= 90)))) (PreH4 : (1 <= (Zlength (flights_data)))) (PreH5 : ((Zlength (flights_data)) <= 100)) (PreH6 : (Pre home_data flights_data)) (PreH7 : (n_pre = (Zlength (flights_data)))) (PreH8 : ((Zlength (flight_rows)) = n_pre)) (PreH9 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((((((Zlength ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3) ∧ ((Zlength ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3)) ∧ ((Zlength ((Znth (i) (flight_rows) ((@List.nil (Option Int)))))) = 16)) ∧ forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < 3)) -> ((((((65 <= (Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int)))) ∧ ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))) <= 90)) ∧ (65 <= (Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))) ∧ ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))) <= 90)) ∧ ((Znth (j_2) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))))) ∧ ((Znth ((5 + j_2)) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))))))) ∧ ((Znth (3) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some (45)))) ∧ ((Znth (4) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some (62)))) ∧ ((Znth (8) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((0 : Int))))))) ,
  TT && emp 
|--
  “ (Spec home_data flights_data (99 :: (111 :: (110 :: (116 :: (101 :: (115 :: (116 :: (@List.nil Int))))))))) ”
  &&  emp
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (flight_rows : (List (List (Option Int)))) (flights_data : (List ((List Int) × (List Int)))) (home_data : (List Int)) (n_pre : Int) (__default__Prod__List_Z__List_Z : _Prod__List_Z__List_Z) (PreH1 : ((Z.land n_pre 1) ≠ (0 : Int))) (PreH2 : ((Zlength (home_data)) = 3)) (PreH3 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < 3)) -> ((65 <= (Znth j home_data (0 : Int))) ∧ ((Znth j home_data (0 : Int)) <= 90)))) (PreH4 : (1 <= (Zlength (flights_data)))) (PreH5 : ((Zlength (flights_data)) <= 100)) (PreH6 : (Pre home_data flights_data)) (PreH7 : (n_pre = (Zlength (flights_data)))) (PreH8 : ((Zlength (flight_rows)) = n_pre)) (PreH9 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((((((Zlength ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3) ∧ ((Zlength ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3)) ∧ ((Zlength ((Znth (i) (flight_rows) ((@List.nil (Option Int)))))) = 16)) ∧ forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < 3)) -> ((((((65 <= (Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int)))) ∧ ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))) <= 90)) ∧ (65 <= (Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))) ∧ ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))) <= 90)) ∧ ((Znth (j_2) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))))) ∧ ((Znth ((5 + j_2)) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))))))) ∧ ((Znth (3) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some (45)))) ∧ ((Znth (4) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some (62)))) ∧ ((Znth (8) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((0 : Int))))))) ,
  (Spec home_data flights_data (99 :: (111 :: (110 :: (116 :: (101 :: (115 :: (116 :: (@List.nil Int)))))))))

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (flight_rows : (List (List (Option Int)))) (flights_data : (List ((List Int) × (List Int)))) (home_data : (List Int)) (home_pre : Int) (flights_pre : Int) (n_pre : Int) (__default__Prod__List_Z__List_Z : _Prod__List_Z__List_Z) (PreH1 : ((Z.land n_pre 1) = (0 : Int))) (PreH2 : ((Zlength (home_data)) = 3)) (PreH3 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < 3)) -> ((65 <= (Znth j home_data (0 : Int))) ∧ ((Znth j home_data (0 : Int)) <= 90)))) (PreH4 : (1 <= (Zlength (flights_data)))) (PreH5 : ((Zlength (flights_data)) <= 100)) (PreH6 : (Pre home_data flights_data)) (PreH7 : (n_pre = (Zlength (flights_data)))) (PreH8 : ((Zlength (flight_rows)) = n_pre)) (PreH9 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((((((Zlength ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3) ∧ ((Zlength ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3)) ∧ ((Zlength ((Znth (i) (flight_rows) ((@List.nil (Option Int)))))) = 16)) ∧ forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < 3)) -> ((((((65 <= (Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int)))) ∧ ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))) <= 90)) ∧ (65 <= (Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))) ∧ ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))) <= 90)) ∧ ((Znth (j_2) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))))) ∧ ((Znth ((5 + j_2)) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))))))) ∧ ((Znth (3) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some (45)))) ∧ ((Znth (4) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some (62)))) ∧ ((Znth (8) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((0 : Int))))))) ,
  (store_string home_pre home_data)
  ** (charArray2.mixed_full flights_pre n_pre 16 flight_rows)
|--
  EX result : (List Int),
  “ (Spec home_data flights_data result) ” &&
  “ (1 = 1) ” &&
  “ (result = (104 :: (111 :: (109 :: (101 :: (@List.nil Int)))))) ”
  &&  (store_string home_pre home_data)
  ** (charArray2.mixed_full flights_pre n_pre 16 flight_rows)
) \/
(
forall (flight_rows : (List (List (Option Int)))) (flights_data : (List ((List Int) × (List Int)))) (home_data : (List Int)) (n_pre : Int) (__default__Prod__List_Z__List_Z : _Prod__List_Z__List_Z) (PreH1 : ((Z.land n_pre 1) = (0 : Int))) (PreH2 : ((Zlength (home_data)) = 3)) (PreH3 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < 3)) -> ((65 <= (Znth j home_data (0 : Int))) ∧ ((Znth j home_data (0 : Int)) <= 90)))) (PreH4 : (1 <= (Zlength (flights_data)))) (PreH5 : ((Zlength (flights_data)) <= 100)) (PreH6 : (Pre home_data flights_data)) (PreH7 : (n_pre = (Zlength (flights_data)))) (PreH8 : ((Zlength (flight_rows)) = n_pre)) (PreH9 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((((((Zlength ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3) ∧ ((Zlength ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3)) ∧ ((Zlength ((Znth (i) (flight_rows) ((@List.nil (Option Int)))))) = 16)) ∧ forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < 3)) -> ((((((65 <= (Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int)))) ∧ ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))) <= 90)) ∧ (65 <= (Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))) ∧ ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))) <= 90)) ∧ ((Znth (j_2) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))))) ∧ ((Znth ((5 + j_2)) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))))))) ∧ ((Znth (3) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some (45)))) ∧ ((Znth (4) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some (62)))) ∧ ((Znth (8) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((0 : Int))))))) ,
  TT && emp 
|--
  “ (Spec home_data flights_data (104 :: (111 :: (109 :: (101 :: (@List.nil Int)))))) ”
  &&  emp
)

noncomputable def solver_return_wit_2_split_goal_1 : Prop :=
  forall (flight_rows : (List (List (Option Int)))) (flights_data : (List ((List Int) × (List Int)))) (home_data : (List Int)) (n_pre : Int) (__default__Prod__List_Z__List_Z : _Prod__List_Z__List_Z) (PreH1 : ((Z.land n_pre 1) = (0 : Int))) (PreH2 : ((Zlength (home_data)) = 3)) (PreH3 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < 3)) -> ((65 <= (Znth j home_data (0 : Int))) ∧ ((Znth j home_data (0 : Int)) <= 90)))) (PreH4 : (1 <= (Zlength (flights_data)))) (PreH5 : ((Zlength (flights_data)) <= 100)) (PreH6 : (Pre home_data flights_data)) (PreH7 : (n_pre = (Zlength (flights_data)))) (PreH8 : ((Zlength (flight_rows)) = n_pre)) (PreH9 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < n_pre)) -> ((((((((Zlength ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3) ∧ ((Zlength ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z))))) = 3)) ∧ ((Zlength ((Znth (i) (flight_rows) ((@List.nil (Option Int)))))) = 16)) ∧ forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < 3)) -> ((((((65 <= (Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int)))) ∧ ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))) <= 90)) ∧ (65 <= (Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))) ∧ ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))) <= 90)) ∧ ((Znth (j_2) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((Znth (j_2) ((fst ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))))) ∧ ((Znth ((5 + j_2)) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((Znth (j_2) ((snd ((Znth i flights_data __default__Prod__List_Z__List_Z)))) ((0 : Int))))))))) ∧ ((Znth (3) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some (45)))) ∧ ((Znth (4) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some (62)))) ∧ ((Znth (8) ((Znth (i) (flight_rows) ((@List.nil (Option Int))))) (None)) = (Some ((0 : Int))))))) ,
  (Spec home_data flights_data (104 :: (111 :: (109 :: (101 :: (@List.nil Int))))))


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P011_765A_neverending_competitions_goal
