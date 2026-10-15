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
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P036_1705C_mark_and_his_unfinished_essay_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (retval = (string_length (text)))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (c_pre = (Zlength (ops)))) (PreH12 : (q_pre = (Zlength (queries_data)))) (PreH13 : ((Zlength (lefts)) = c_pre)) (PreH14 : ((Zlength (rights)) = c_pre)) (PreH15 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < c_pre)) -> (((fst ((Znth i_2 ops __default__Prod_Z_Z))) = (Znth i_2 lefts 0)) /\ ((snd ((Znth i_2 ops __default__Prod_Z_Z))) = (Znth i_2 rights 0))))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (store_string s_pre text )
  **  ((( &( "length" ) )) # Int64  |-> retval)
  **  (Int64Array.undef_full ( &( "before" ) ) 40 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data: (@list Z)) (length: Z) (i: Z) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (i < c_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (0 <= i)) (PreH18 : (i <= c_pre)) (PreH19 : (length = (Zlength ((Znth i states __default__List_Z))))) (PreH20 : (1 <= length)) (PreH21 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH22 : (StateLengthsPrefix states i before_data )) ,
  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.seg ( &( "before" ) ) 0 (i + 1 ) (app (before_data) ((cons (length) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ ((length + (((Znth i rights 0) - (Znth i lefts 0) ) + 1 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (length + (((Znth i rights 0) - (Znth i lefts 0) ) + 1 ) )) ”
) \/
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data: (@list Z)) (length: Z) (i: Z) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (i < c_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (0 <= i)) (PreH18 : (i <= c_pre)) (PreH19 : (length = (Zlength ((Znth i states __default__List_Z))))) (PreH20 : (1 <= length)) (PreH21 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH22 : (StateLengthsPrefix states i before_data )) ,
  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.seg ( &( "before" ) ) 0 (i + 1 ) (app (before_data) ((cons (length) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ ((length + (((Znth i rights 0) - (Znth i lefts 0) ) + 1 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (length + (((Znth i rights 0) - (Znth i lefts 0) ) + 1 ) )) ”
).

Definition solver_safety_wit_2_split_goal_1 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data: (@list Z)) (length: Z) (i: Z) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (i < c_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (0 <= i)) (PreH18 : (i <= c_pre)) (PreH19 : (length = (Zlength ((Znth i states __default__List_Z))))) (PreH20 : (1 <= length)) (PreH21 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH22 : (StateLengthsPrefix states i before_data )) ,
  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.seg ( &( "before" ) ) 0 (i + 1 ) (app (before_data) ((cons (length) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ ((length + (((Znth i rights 0) - (Znth i lefts 0) ) + 1 ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_2_split_goal_2 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data: (@list Z)) (length: Z) (i: Z) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (i < c_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (0 <= i)) (PreH18 : (i <= c_pre)) (PreH19 : (length = (Zlength ((Znth i states __default__List_Z))))) (PreH20 : (1 <= length)) (PreH21 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH22 : (StateLengthsPrefix states i before_data )) ,
  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.seg ( &( "before" ) ) 0 (i + 1 ) (app (before_data) ((cons (length) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ ((INT64_MIN) <= (length + (((Znth i rights 0) - (Znth i lefts 0) ) + 1 ) )) ”
.

Definition solver_safety_wit_3 := 
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data: (@list Z)) (length: Z) (i: Z) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (i < c_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (0 <= i)) (PreH18 : (i <= c_pre)) (PreH19 : (length = (Zlength ((Znth i states __default__List_Z))))) (PreH20 : (1 <= length)) (PreH21 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH22 : (StateLengthsPrefix states i before_data )) ,
  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.seg ( &( "before" ) ) 0 (i + 1 ) (app (before_data) ((cons (length) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ ((((Znth i rights 0) - (Znth i lefts 0) ) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((Znth i rights 0) - (Znth i lefts 0) ) + 1 )) ”
) \/
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data: (@list Z)) (length: Z) (i: Z) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (i < c_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (0 <= i)) (PreH18 : (i <= c_pre)) (PreH19 : (length = (Zlength ((Znth i states __default__List_Z))))) (PreH20 : (1 <= length)) (PreH21 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH22 : (StateLengthsPrefix states i before_data )) ,
  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.seg ( &( "before" ) ) 0 (i + 1 ) (app (before_data) ((cons (length) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ ((((Znth i rights 0) - (Znth i lefts 0) ) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((Znth i rights 0) - (Znth i lefts 0) ) + 1 )) ”
).

Definition solver_safety_wit_3_split_goal_1 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data: (@list Z)) (length: Z) (i: Z) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (i < c_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (0 <= i)) (PreH18 : (i <= c_pre)) (PreH19 : (length = (Zlength ((Znth i states __default__List_Z))))) (PreH20 : (1 <= length)) (PreH21 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH22 : (StateLengthsPrefix states i before_data )) ,
  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.seg ( &( "before" ) ) 0 (i + 1 ) (app (before_data) ((cons (length) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ ((((Znth i rights 0) - (Znth i lefts 0) ) + 1 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_3_split_goal_2 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data: (@list Z)) (length: Z) (i: Z) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (i < c_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (0 <= i)) (PreH18 : (i <= c_pre)) (PreH19 : (length = (Zlength ((Znth i states __default__List_Z))))) (PreH20 : (1 <= length)) (PreH21 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH22 : (StateLengthsPrefix states i before_data )) ,
  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.seg ( &( "before" ) ) 0 (i + 1 ) (app (before_data) ((cons (length) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ ((INT64_MIN) <= (((Znth i rights 0) - (Znth i lefts 0) ) + 1 )) ”
.

Definition solver_safety_wit_4 := 
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data: (@list Z)) (length: Z) (i: Z) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (i < c_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (0 <= i)) (PreH18 : (i <= c_pre)) (PreH19 : (length = (Zlength ((Znth i states __default__List_Z))))) (PreH20 : (1 <= length)) (PreH21 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH22 : (StateLengthsPrefix states i before_data )) ,
  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.seg ( &( "before" ) ) 0 (i + 1 ) (app (before_data) ((cons (length) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ (((Znth i rights 0) - (Znth i lefts 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i rights 0) - (Znth i lefts 0) )) ”
) \/
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data: (@list Z)) (length: Z) (i: Z) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (i < c_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (0 <= i)) (PreH18 : (i <= c_pre)) (PreH19 : (length = (Zlength ((Znth i states __default__List_Z))))) (PreH20 : (1 <= length)) (PreH21 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH22 : (StateLengthsPrefix states i before_data )) ,
  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.seg ( &( "before" ) ) 0 (i + 1 ) (app (before_data) ((cons (length) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ (((Znth i rights 0) - (Znth i lefts 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i rights 0) - (Znth i lefts 0) )) ”
).

Definition solver_safety_wit_4_split_goal_1 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data: (@list Z)) (length: Z) (i: Z) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (i < c_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (0 <= i)) (PreH18 : (i <= c_pre)) (PreH19 : (length = (Zlength ((Znth i states __default__List_Z))))) (PreH20 : (1 <= length)) (PreH21 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH22 : (StateLengthsPrefix states i before_data )) ,
  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.seg ( &( "before" ) ) 0 (i + 1 ) (app (before_data) ((cons (length) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ (((Znth i rights 0) - (Znth i lefts 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_4_split_goal_2 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data: (@list Z)) (length: Z) (i: Z) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (i < c_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (0 <= i)) (PreH18 : (i <= c_pre)) (PreH19 : (length = (Zlength ((Znth i states __default__List_Z))))) (PreH20 : (1 <= length)) (PreH21 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH22 : (StateLengthsPrefix states i before_data )) ,
  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.seg ( &( "before" ) ) 0 (i + 1 ) (app (before_data) ((cons (length) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ ((INT64_MIN) <= ((Znth i rights 0) - (Znth i lefts 0) )) ”
.

Definition solver_safety_wit_5 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data: (@list Z)) (length: Z) (i: Z) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (i < c_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (0 <= i)) (PreH18 : (i <= c_pre)) (PreH19 : (length = (Zlength ((Znth i states __default__List_Z))))) (PreH20 : (1 <= length)) (PreH21 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH22 : (StateLengthsPrefix states i before_data )) ,
  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.seg ( &( "before" ) ) 0 (i + 1 ) (app (before_data) ((cons (length) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data: (@list Z)) (length: Z) (i: Z) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (i < c_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (0 <= i)) (PreH18 : (i <= c_pre)) (PreH19 : (length = (Zlength ((Znth i states __default__List_Z))))) (PreH20 : (1 <= length)) (PreH21 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH22 : (StateLengthsPrefix states i before_data )) ,
  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.seg ( &( "before" ) ) 0 (i + 1 ) (app (before_data) ((cons (length) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "length" ) )) # Int64  |-> (length + (((Znth i rights 0) - (Znth i lefts 0) ) + 1 ) ))
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_7 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data: (@list Z)) (length: Z) (i: Z) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i >= c_pre)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : (1 <= (Zlength (ops)))) (PreH5 : ((Zlength (ops)) <= 40)) (PreH6 : (1 <= (Zlength (queries_data)))) (PreH7 : ((Zlength (queries_data)) <= 10000)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH9 : (Pre text ops queries_data )) (PreH10 : (CopyPasteStates text ops states )) (PreH11 : (c_pre = (Zlength (ops)))) (PreH12 : (q_pre = (Zlength (queries_data)))) (PreH13 : ((Zlength (lefts)) = c_pre)) (PreH14 : ((Zlength (rights)) = c_pre)) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH16 : (0 <= i)) (PreH17 : (i <= c_pre)) (PreH18 : (length = (Zlength ((Znth i states __default__List_Z))))) (PreH19 : (1 <= length)) (PreH20 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH21 : (StateLengthsPrefix states i before_data )) ,
  ((( &( "z" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 i before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) i 40 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (z < q_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (StateLengthsPrefix states c_pre before_data )) (PreH18 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH19 : (0 <= z)) (PreH20 : (z <= q_pre)) (PreH21 : (AnswerPrefix text ops queries_data z out )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "k" ) )) # Int64  |-> (Znth z queries_data 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ ((c_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c_pre - 1 )) ”
.

Definition solver_safety_wit_9 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (z < q_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (StateLengthsPrefix states c_pre before_data )) (PreH18 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH19 : (0 <= z)) (PreH20 : (z <= q_pre)) (PreH21 : (AnswerPrefix text ops queries_data z out )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "k" ) )) # Int64  |-> (Znth z queries_data 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : (1 <= (Zlength (ops)))) (PreH4 : ((Zlength (ops)) <= 40)) (PreH5 : (1 <= (Zlength (queries_data)))) (PreH6 : ((Zlength (queries_data)) <= 10000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH8 : (Pre text ops queries_data )) (PreH9 : (CopyPasteStates text ops states )) (PreH10 : (c_pre = (Zlength (ops)))) (PreH11 : (q_pre = (Zlength (queries_data)))) (PreH12 : ((Zlength (lefts)) = c_pre)) (PreH13 : ((Zlength (rights)) = c_pre)) (PreH14 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH15 : (StateLengthsPrefix states c_pre before_data )) (PreH16 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH17 : (0 <= z)) (PreH18 : (z < q_pre)) (PreH19 : (AnswerPrefix text ops queries_data z out )) (PreH20 : ((-1) <= i)) (PreH21 : (i < c_pre)) (PreH22 : (BacktrackedPosition states (Znth z queries_data 0) i k )) (PreH23 : (1 <= k)) (PreH24 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_11 := 
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k > (Znth (i - 0 ) before_data 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states c_pre before_data )) (PreH19 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ (((((Znth i lefts 0) + k ) - (Znth (i - 0 ) before_data 0) ) - 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth i lefts 0) + k ) - (Znth (i - 0 ) before_data 0) ) - 1 )) ”
) \/
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k > (Znth (i - 0 ) before_data 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states c_pre before_data )) (PreH19 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ (((((Znth i lefts 0) + k ) - (Znth (i - 0 ) before_data 0) ) - 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth i lefts 0) + k ) - (Znth (i - 0 ) before_data 0) ) - 1 )) ”
).

Definition solver_safety_wit_11_split_goal_1 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k > (Znth (i - 0 ) before_data 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states c_pre before_data )) (PreH19 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ (((((Znth i lefts 0) + k ) - (Znth (i - 0 ) before_data 0) ) - 1 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_11_split_goal_2 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k > (Znth (i - 0 ) before_data 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states c_pre before_data )) (PreH19 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ ((INT64_MIN) <= ((((Znth i lefts 0) + k ) - (Znth (i - 0 ) before_data 0) ) - 1 )) ”
.

Definition solver_safety_wit_12 := 
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k > (Znth (i - 0 ) before_data 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states c_pre before_data )) (PreH19 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ ((((Znth i lefts 0) + k ) - (Znth (i - 0 ) before_data 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((Znth i lefts 0) + k ) - (Znth (i - 0 ) before_data 0) )) ”
) \/
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k > (Znth (i - 0 ) before_data 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states c_pre before_data )) (PreH19 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ ((((Znth i lefts 0) + k ) - (Znth (i - 0 ) before_data 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((Znth i lefts 0) + k ) - (Znth (i - 0 ) before_data 0) )) ”
).

Definition solver_safety_wit_12_split_goal_1 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k > (Znth (i - 0 ) before_data 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states c_pre before_data )) (PreH19 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ ((((Znth i lefts 0) + k ) - (Znth (i - 0 ) before_data 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_12_split_goal_2 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k > (Znth (i - 0 ) before_data 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states c_pre before_data )) (PreH19 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ ((INT64_MIN) <= (((Znth i lefts 0) + k ) - (Znth (i - 0 ) before_data 0) )) ”
.

Definition solver_safety_wit_13 := 
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k > (Znth (i - 0 ) before_data 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states c_pre before_data )) (PreH19 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ (((Znth i lefts 0) + k ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i lefts 0) + k )) ”
) \/
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k > (Znth (i - 0 ) before_data 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states c_pre before_data )) (PreH19 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ (((Znth i lefts 0) + k ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i lefts 0) + k )) ”
).

Definition solver_safety_wit_13_split_goal_1 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k > (Znth (i - 0 ) before_data 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states c_pre before_data )) (PreH19 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ (((Znth i lefts 0) + k ) <= INT64_MAX) ”
.

Definition solver_safety_wit_13_split_goal_2 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k > (Znth (i - 0 ) before_data 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states c_pre before_data )) (PreH19 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ ((INT64_MIN) <= ((Znth i lefts 0) + k )) ”
.

Definition solver_safety_wit_14 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k > (Znth (i - 0 ) before_data 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states c_pre before_data )) (PreH19 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_15 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k > (Znth (i - 0 ) before_data 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states c_pre before_data )) (PreH19 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int64  |-> ((((Znth i lefts 0) + k ) - (Znth (i - 0 ) before_data 0) ) - 1 ))
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_16 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k <= (Znth (i - 0 ) before_data 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states c_pre before_data )) (PreH19 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_17 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (states: (@list (@list Z))) (before_data: (@list Z)) (out: (@list Z)) (length: Z) (z: Z) (k: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : (1 <= (Zlength (ops)))) (PreH4 : ((Zlength (ops)) <= 40)) (PreH5 : (1 <= (Zlength (queries_data)))) (PreH6 : ((Zlength (queries_data)) <= 10000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH8 : (Pre text ops queries_data )) (PreH9 : (CopyPasteStates text ops states )) (PreH10 : (c_pre = (Zlength (ops)))) (PreH11 : (q_pre = (Zlength (queries_data)))) (PreH12 : ((Zlength (lefts)) = c_pre)) (PreH13 : ((Zlength (rights)) = c_pre)) (PreH14 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH15 : (StateLengthsPrefix states c_pre before_data )) (PreH16 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH17 : (0 <= z)) (PreH18 : (z < q_pre)) (PreH19 : (AnswerPrefix text ops queries_data z out )) (PreH20 : (1 <= k)) (PreH21 : (k <= (Zlength (text)))) (PreH22 : (FinalCharacter text ops (Znth z queries_data 0) (Znth (k - 1 ) text 0) )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ ((k - 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (k - 1 )) ”
.

Definition solver_safety_wit_18 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (states: (@list (@list Z))) (before_data: (@list Z)) (out: (@list Z)) (length: Z) (z: Z) (k: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : (1 <= (Zlength (ops)))) (PreH4 : ((Zlength (ops)) <= 40)) (PreH5 : (1 <= (Zlength (queries_data)))) (PreH6 : ((Zlength (queries_data)) <= 10000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH8 : (Pre text ops queries_data )) (PreH9 : (CopyPasteStates text ops states )) (PreH10 : (c_pre = (Zlength (ops)))) (PreH11 : (q_pre = (Zlength (queries_data)))) (PreH12 : ((Zlength (lefts)) = c_pre)) (PreH13 : ((Zlength (rights)) = c_pre)) (PreH14 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH15 : (StateLengthsPrefix states c_pre before_data )) (PreH16 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH17 : (0 <= z)) (PreH18 : (z < q_pre)) (PreH19 : (AnswerPrefix text ops queries_data z out )) (PreH20 : (1 <= k)) (PreH21 : (k <= (Zlength (text)))) (PreH22 : (FinalCharacter text ops (Znth z queries_data 0) (Znth (k - 1 ) text 0) )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "k" ) )) # Int64  |-> k)
  **  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_19 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (states: (@list (@list Z))) (before_data: (@list Z)) (out: (@list Z)) (length: Z) (z: Z) (k: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : (1 <= (Zlength (ops)))) (PreH5 : ((Zlength (ops)) <= 40)) (PreH6 : (1 <= (Zlength (queries_data)))) (PreH7 : ((Zlength (queries_data)) <= 10000)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH9 : (Pre text ops queries_data )) (PreH10 : (CopyPasteStates text ops states )) (PreH11 : (c_pre = (Zlength (ops)))) (PreH12 : (q_pre = (Zlength (queries_data)))) (PreH13 : ((Zlength (lefts)) = c_pre)) (PreH14 : ((Zlength (rights)) = c_pre)) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH16 : (StateLengthsPrefix states c_pre before_data )) (PreH17 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH18 : (0 <= z)) (PreH19 : (z < q_pre)) (PreH20 : (AnswerPrefix text ops queries_data z out )) (PreH21 : (1 <= k)) (PreH22 : (k <= (Zlength (text)))) (PreH23 : (FinalCharacter text ops (Znth z queries_data 0) (Znth (k - 1 ) text 0) )) ,
  (CharArray.seg answers_pre 0 (z + 1 ) (app (out) ((cons ((Znth (k - 1 ) (c_string (text)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg answers_pre (z + 1 ) q_pre )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  ((( &( "length" ) )) # Int64  |-> length)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ ((z + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (z + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (retval: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (retval = (string_length (text)))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (c_pre = (Zlength (ops)))) (PreH12 : (q_pre = (Zlength (queries_data)))) (PreH13 : ((Zlength (lefts)) = c_pre)) (PreH14 : ((Zlength (rights)) = c_pre)) (PreH15 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < c_pre)) -> (((fst ((Znth i_2 ops __default__Prod_Z_Z))) = (Znth i_2 lefts 0)) /\ ((snd ((Znth i_2 ops __default__Prod_Z_Z))) = (Znth i_2 rights 0))))) ,
  (store_string s_pre text )
  **  (Int64Array.undef_full ( &( "before" ) ) 40 )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  EX (before_data: (@list Z))  (states: (@list (@list Z))) ,
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ (1 <= (Zlength (ops))) ” 
  &&  “ ((Zlength (ops)) <= 40) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 10000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (Pre text ops queries_data ) ” 
  &&  “ (CopyPasteStates text ops states ) ” 
  &&  “ (c_pre = (Zlength (ops))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ ((Zlength (lefts)) = c_pre) ” 
  &&  “ ((Zlength (rights)) = c_pre) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0)))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (retval = (Zlength ((Znth 0 states __default__List_Z)))) ” 
  &&  “ (1 <= retval) ” 
  &&  “ (retval <= (200000 * (Z.pow (2) (40)) )) ” 
  &&  “ (StateLengthsPrefix states 0 before_data ) ”
  &&  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 0 before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) 0 40 )
) \/
(
forall (q_pre: Z) (c_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (retval: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (retval = (string_length (text)))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (c_pre = (Zlength (ops)))) (PreH12 : (q_pre = (Zlength (queries_data)))) (PreH13 : ((Zlength (lefts)) = c_pre)) (PreH14 : ((Zlength (rights)) = c_pre)) (PreH15 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < c_pre)) -> (((fst ((Znth i_2 ops __default__Prod_Z_Z))) = (Znth i_2 lefts 0)) /\ ((snd ((Znth i_2 ops __default__Prod_Z_Z))) = (Znth i_2 rights 0))))) ,
  TT && emp 
|--
  EX (states: (@list (@list Z))) ,
  “ (CopyPasteStates text ops states ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength (ops))) ” 
  &&  “ ((string_length (text)) = (Zlength ((Znth 0 states __default__List_Z)))) ” 
  &&  “ (1 <= (string_length (text))) ” 
  &&  “ ((string_length (text)) <= (200000 * (Z.pow (2) (40)) )) ” 
  &&  “ (StateLengthsPrefix states 0 (@nil Z) ) ”
  &&  emp
).

Definition solver_entail_wit_2 := 
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data_2: (@list Z)) (length: Z) (i: Z) (states_2: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (i < c_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states_2 )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (0 <= i)) (PreH18 : (i <= c_pre)) (PreH19 : (length = (Zlength ((Znth i states_2 __default__List_Z))))) (PreH20 : (1 <= length)) (PreH21 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH22 : (StateLengthsPrefix states_2 i before_data_2 )) ,
  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.seg ( &( "before" ) ) 0 (i + 1 ) (app (before_data_2) ((cons (length) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  EX (before_data: (@list Z))  (states: (@list (@list Z))) ,
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ (1 <= (Zlength (ops))) ” 
  &&  “ ((Zlength (ops)) <= 40) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 10000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (Pre text ops queries_data ) ” 
  &&  “ (CopyPasteStates text ops states ) ” 
  &&  “ (c_pre = (Zlength (ops))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ ((Zlength (lefts)) = c_pre) ” 
  &&  “ ((Zlength (rights)) = c_pre) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0)))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= c_pre) ” 
  &&  “ ((length + (((Znth i rights 0) - (Znth i lefts 0) ) + 1 ) ) = (Zlength ((Znth (i + 1 ) states __default__List_Z)))) ” 
  &&  “ (1 <= (length + (((Znth i rights 0) - (Znth i lefts 0) ) + 1 ) )) ” 
  &&  “ ((length + (((Znth i rights 0) - (Znth i lefts 0) ) + 1 ) ) <= (200000 * (Z.pow (2) (40)) )) ” 
  &&  “ (StateLengthsPrefix states (i + 1 ) before_data ) ”
  &&  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 (i + 1 ) before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
) \/
(
forall (q_pre: Z) (c_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data_2: (@list Z)) (length: Z) (i: Z) (states_2: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (i < c_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states_2 )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (0 <= i)) (PreH18 : (i <= c_pre)) (PreH19 : (length = (Zlength ((Znth i states_2 __default__List_Z))))) (PreH20 : (1 <= length)) (PreH21 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH22 : (StateLengthsPrefix states_2 i before_data_2 )) ,
  TT && emp 
|--
  EX (states: (@list (@list Z))) ,
  “ (CopyPasteStates text ops states ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (ops))) ” 
  &&  “ (((Zlength ((Znth i states_2 __default__List_Z))) + (((Znth i rights 0) - (Znth i lefts 0) ) + 1 ) ) = (Zlength ((Znth (i + 1 ) states __default__List_Z)))) ” 
  &&  “ (1 <= ((Zlength ((Znth i states_2 __default__List_Z))) + (((Znth i rights 0) - (Znth i lefts 0) ) + 1 ) )) ” 
  &&  “ (((Zlength ((Znth i states_2 __default__List_Z))) + (((Znth i rights 0) - (Znth i lefts 0) ) + 1 ) ) <= (200000 * (Z.pow (2) (40)) )) ” 
  &&  “ (StateLengthsPrefix states (i + 1 ) (app (before_data_2) ((cons ((Zlength ((Znth i states_2 __default__List_Z)))) ((@nil Z))))) ) ”
  &&  emp
).

Definition solver_entail_wit_3 := 
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data_2: (@list Z)) (length: Z) (i: Z) (states_2: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i >= c_pre)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : (1 <= (Zlength (ops)))) (PreH5 : ((Zlength (ops)) <= 40)) (PreH6 : (1 <= (Zlength (queries_data)))) (PreH7 : ((Zlength (queries_data)) <= 10000)) (PreH8 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (Zlength (text)))) -> ((97 <= (Znth j_3 text 0)) /\ ((Znth j_3 text 0) <= 122)))) (PreH9 : (Pre text ops queries_data )) (PreH10 : (CopyPasteStates text ops states_2 )) (PreH11 : (c_pre = (Zlength (ops)))) (PreH12 : (q_pre = (Zlength (queries_data)))) (PreH13 : ((Zlength (lefts)) = c_pre)) (PreH14 : ((Zlength (rights)) = c_pre)) (PreH15 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < c_pre)) -> (((fst ((Znth j_4 ops __default__Prod_Z_Z))) = (Znth j_4 lefts 0)) /\ ((snd ((Znth j_4 ops __default__Prod_Z_Z))) = (Znth j_4 rights 0))))) (PreH16 : (0 <= i)) (PreH17 : (i <= c_pre)) (PreH18 : (length = (Zlength ((Znth i states_2 __default__List_Z))))) (PreH19 : (1 <= length)) (PreH20 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH21 : (StateLengthsPrefix states_2 i before_data_2 )) ,
  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 i before_data_2 )
  **  (Int64Array.undef_seg ( &( "before" ) ) i 40 )
|--
  EX (out: (@list Z))  (before_data: (@list Z))  (states: (@list (@list Z))) ,
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ (1 <= (Zlength (ops))) ” 
  &&  “ ((Zlength (ops)) <= 40) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 10000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (Pre text ops queries_data ) ” 
  &&  “ (CopyPasteStates text ops states ) ” 
  &&  “ (c_pre = (Zlength (ops))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ ((Zlength (lefts)) = c_pre) ” 
  &&  “ ((Zlength (rights)) = c_pre) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0)))) ” 
  &&  “ (StateLengthsPrefix states c_pre before_data ) ” 
  &&  “ (length = (Zlength ((Znth c_pre states __default__List_Z)))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (AnswerPrefix text ops queries_data 0 out ) ”
  &&  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 0 out )
  **  (CharArray.undef_seg answers_pre 0 q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
) \/
(
forall (q_pre: Z) (c_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data_2: (@list Z)) (length: Z) (i: Z) (states_2: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (i >= c_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (Zlength (text)))) -> ((97 <= (Znth j_3 text 0)) /\ ((Znth j_3 text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states_2 )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < c_pre)) -> (((fst ((Znth j_4 ops __default__Prod_Z_Z))) = (Znth j_4 lefts 0)) /\ ((snd ((Znth j_4 ops __default__Prod_Z_Z))) = (Znth j_4 rights 0))))) (PreH17 : (0 <= i)) (PreH18 : (i <= c_pre)) (PreH19 : (length = (Zlength ((Znth i states_2 __default__List_Z))))) (PreH20 : (1 <= length)) (PreH21 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH22 : (StateLengthsPrefix states_2 i before_data_2 )) ,
  (Int64Array.seg ( &( "before" ) ) 0 i before_data_2 )
|--
  EX (before_data: (@list Z))  (states: (@list (@list Z))) ,
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ (1 <= (Zlength (ops))) ” 
  &&  “ ((Zlength (ops)) <= 40) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 10000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (Pre text ops queries_data ) ” 
  &&  “ (CopyPasteStates text ops states ) ” 
  &&  “ (c_pre = (Zlength (ops))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ ((Zlength (lefts)) = c_pre) ” 
  &&  “ ((Zlength (rights)) = c_pre) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0)))) ” 
  &&  “ (StateLengthsPrefix states c_pre before_data ) ” 
  &&  “ (length = (Zlength ((Znth c_pre states __default__List_Z)))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (AnswerPrefix text ops queries_data 0 (@nil Z) ) ”
  &&  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
).

Definition solver_entail_wit_4 := 
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (out_2: (@list Z)) (z: Z) (length: Z) (before_data_2: (@list Z)) (states_2: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (z < q_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (Zlength (text)))) -> ((97 <= (Znth j_3 text 0)) /\ ((Znth j_3 text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states_2 )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < c_pre)) -> (((fst ((Znth j_4 ops __default__Prod_Z_Z))) = (Znth j_4 lefts 0)) /\ ((snd ((Znth j_4 ops __default__Prod_Z_Z))) = (Znth j_4 rights 0))))) (PreH17 : (StateLengthsPrefix states_2 c_pre before_data_2 )) (PreH18 : (length = (Zlength ((Znth c_pre states_2 __default__List_Z))))) (PreH19 : (0 <= z)) (PreH20 : (z <= q_pre)) (PreH21 : (AnswerPrefix text ops queries_data z out_2 )) ,
  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (CharArray.seg answers_pre 0 z out_2 )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data_2 )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  EX (out: (@list Z))  (before_data: (@list Z))  (states: (@list (@list Z))) ,
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ (1 <= (Zlength (ops))) ” 
  &&  “ ((Zlength (ops)) <= 40) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 10000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (Pre text ops queries_data ) ” 
  &&  “ (CopyPasteStates text ops states ) ” 
  &&  “ (c_pre = (Zlength (ops))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ ((Zlength (lefts)) = c_pre) ” 
  &&  “ ((Zlength (rights)) = c_pre) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0)))) ” 
  &&  “ (StateLengthsPrefix states c_pre before_data ) ” 
  &&  “ (length = (Zlength ((Znth c_pre states __default__List_Z)))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < q_pre) ” 
  &&  “ (AnswerPrefix text ops queries_data z out ) ” 
  &&  “ ((-1) <= (c_pre - 1 )) ” 
  &&  “ ((c_pre - 1 ) < c_pre) ” 
  &&  “ (BacktrackedPosition states (Znth z queries_data 0) (c_pre - 1 ) (Znth z queries_data 0) ) ” 
  &&  “ (1 <= (Znth z queries_data 0)) ” 
  &&  “ ((Znth z queries_data 0) <= (200000 * (Z.pow (2) (40)) )) ”
  &&  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
) \/
(
forall (q_pre: Z) (c_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (out_2: (@list Z)) (z: Z) (length: Z) (before_data_2: (@list Z)) (states_2: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (z < q_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (Zlength (text)))) -> ((97 <= (Znth j_3 text 0)) /\ ((Znth j_3 text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states_2 )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < c_pre)) -> (((fst ((Znth j_4 ops __default__Prod_Z_Z))) = (Znth j_4 lefts 0)) /\ ((snd ((Znth j_4 ops __default__Prod_Z_Z))) = (Znth j_4 rights 0))))) (PreH17 : (StateLengthsPrefix states_2 c_pre before_data_2 )) (PreH18 : (length = (Zlength ((Znth c_pre states_2 __default__List_Z))))) (PreH19 : (0 <= z)) (PreH20 : (z <= q_pre)) (PreH21 : (AnswerPrefix text ops queries_data z out_2 )) ,
  TT && emp 
|--
  EX (states: (@list (@list Z))) ,
  “ (CopyPasteStates text ops states ) ” 
  &&  “ (StateLengthsPrefix states (Zlength (ops)) before_data_2 ) ” 
  &&  “ ((Zlength ((Znth c_pre states_2 __default__List_Z))) = (Zlength ((Znth (Zlength (ops)) states __default__List_Z)))) ” 
  &&  “ ((-1) <= ((Zlength (ops)) - 1 )) ” 
  &&  “ (((Zlength (ops)) - 1 ) < (Zlength (ops))) ” 
  &&  “ (BacktrackedPosition states (Znth z queries_data 0) ((Zlength (ops)) - 1 ) (Znth z queries_data 0) ) ” 
  &&  “ (1 <= (Znth z queries_data 0)) ” 
  &&  “ ((Znth z queries_data 0) <= (200000 * (Z.pow (2) (40)) )) ”
  &&  emp
).

Definition solver_entail_wit_5 := 
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out_2: (@list Z)) (z: Z) (length: Z) (before_data_2: (@list Z)) (states_2: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i < 0)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : (1 <= (Zlength (ops)))) (PreH5 : ((Zlength (ops)) <= 40)) (PreH6 : (1 <= (Zlength (queries_data)))) (PreH7 : ((Zlength (queries_data)) <= 10000)) (PreH8 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (Zlength (text)))) -> ((97 <= (Znth j_3 text 0)) /\ ((Znth j_3 text 0) <= 122)))) (PreH9 : (Pre text ops queries_data )) (PreH10 : (CopyPasteStates text ops states_2 )) (PreH11 : (c_pre = (Zlength (ops)))) (PreH12 : (q_pre = (Zlength (queries_data)))) (PreH13 : ((Zlength (lefts)) = c_pre)) (PreH14 : ((Zlength (rights)) = c_pre)) (PreH15 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < c_pre)) -> (((fst ((Znth j_4 ops __default__Prod_Z_Z))) = (Znth j_4 lefts 0)) /\ ((snd ((Znth j_4 ops __default__Prod_Z_Z))) = (Znth j_4 rights 0))))) (PreH16 : (StateLengthsPrefix states_2 c_pre before_data_2 )) (PreH17 : (length = (Zlength ((Znth c_pre states_2 __default__List_Z))))) (PreH18 : (0 <= z)) (PreH19 : (z < q_pre)) (PreH20 : (AnswerPrefix text ops queries_data z out_2 )) (PreH21 : ((-1) <= i)) (PreH22 : (i < c_pre)) (PreH23 : (BacktrackedPosition states_2 (Znth z queries_data 0) i k )) (PreH24 : (1 <= k)) (PreH25 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out_2 )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data_2 )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  EX (out: (@list Z))  (before_data: (@list Z))  (states: (@list (@list Z))) ,
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ (1 <= (Zlength (ops))) ” 
  &&  “ ((Zlength (ops)) <= 40) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 10000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (Pre text ops queries_data ) ” 
  &&  “ (CopyPasteStates text ops states ) ” 
  &&  “ (c_pre = (Zlength (ops))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ ((Zlength (lefts)) = c_pre) ” 
  &&  “ ((Zlength (rights)) = c_pre) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0)))) ” 
  &&  “ (StateLengthsPrefix states c_pre before_data ) ” 
  &&  “ (length = (Zlength ((Znth c_pre states __default__List_Z)))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < q_pre) ” 
  &&  “ (AnswerPrefix text ops queries_data z out ) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= (Zlength (text))) ” 
  &&  “ (FinalCharacter text ops (Znth z queries_data 0) (Znth (k - 1 ) text 0) ) ”
  &&  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
) \/
(
forall (q_pre: Z) (c_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out_2: (@list Z)) (z: Z) (length: Z) (before_data_2: (@list Z)) (states_2: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (i < 0)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (Zlength (text)))) -> ((97 <= (Znth j_3 text 0)) /\ ((Znth j_3 text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states_2 )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < c_pre)) -> (((fst ((Znth j_4 ops __default__Prod_Z_Z))) = (Znth j_4 lefts 0)) /\ ((snd ((Znth j_4 ops __default__Prod_Z_Z))) = (Znth j_4 rights 0))))) (PreH17 : (StateLengthsPrefix states_2 c_pre before_data_2 )) (PreH18 : (length = (Zlength ((Znth c_pre states_2 __default__List_Z))))) (PreH19 : (0 <= z)) (PreH20 : (z < q_pre)) (PreH21 : (AnswerPrefix text ops queries_data z out_2 )) (PreH22 : ((-1) <= i)) (PreH23 : (i < c_pre)) (PreH24 : (BacktrackedPosition states_2 (Znth z queries_data 0) i k )) (PreH25 : (1 <= k)) (PreH26 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  TT && emp 
|--
  EX (states: (@list (@list Z))) ,
  “ (CopyPasteStates text ops states ) ” 
  &&  “ (StateLengthsPrefix states (Zlength (ops)) before_data_2 ) ” 
  &&  “ ((Zlength ((Znth c_pre states_2 __default__List_Z))) = (Zlength ((Znth (Zlength (ops)) states __default__List_Z)))) ” 
  &&  “ (k <= (Zlength (text))) ” 
  &&  “ (FinalCharacter text ops (Znth z queries_data 0) (Znth (k - 1 ) text 0) ) ”
  &&  emp
).

Definition solver_entail_wit_6_1 := 
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out_2: (@list Z)) (z: Z) (length: Z) (before_data_2: (@list Z)) (states_2: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k > (Znth (i - 0 ) before_data_2 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states_2 )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states_2 c_pre before_data_2 )) (PreH19 : (length = (Zlength ((Znth c_pre states_2 __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out_2 )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states_2 (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data_2 )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out_2 )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  EX (out: (@list Z))  (before_data: (@list Z))  (states: (@list (@list Z))) ,
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ (1 <= (Zlength (ops))) ” 
  &&  “ ((Zlength (ops)) <= 40) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 10000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (Pre text ops queries_data ) ” 
  &&  “ (CopyPasteStates text ops states ) ” 
  &&  “ (c_pre = (Zlength (ops))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ ((Zlength (lefts)) = c_pre) ” 
  &&  “ ((Zlength (rights)) = c_pre) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0)))) ” 
  &&  “ (StateLengthsPrefix states c_pre before_data ) ” 
  &&  “ (length = (Zlength ((Znth c_pre states __default__List_Z)))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < q_pre) ” 
  &&  “ (AnswerPrefix text ops queries_data z out ) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < c_pre) ” 
  &&  “ (BacktrackedPosition states (Znth z queries_data 0) (i - 1 ) ((((Znth i lefts 0) + k ) - (Znth (i - 0 ) before_data_2 0) ) - 1 ) ) ” 
  &&  “ (1 <= ((((Znth i lefts 0) + k ) - (Znth (i - 0 ) before_data_2 0) ) - 1 )) ” 
  &&  “ (((((Znth i lefts 0) + k ) - (Znth (i - 0 ) before_data_2 0) ) - 1 ) <= (200000 * (Z.pow (2) (40)) )) ”
  &&  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
) \/
(
forall (q_pre: Z) (c_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out_2: (@list Z)) (z: Z) (length: Z) (before_data_2: (@list Z)) (states_2: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k > (Znth (i - 0 ) before_data_2 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states_2 )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states_2 c_pre before_data_2 )) (PreH19 : (length = (Zlength ((Znth c_pre states_2 __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out_2 )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states_2 (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  TT && emp 
|--
  EX (states: (@list (@list Z))) ,
  “ (CopyPasteStates text ops states ) ” 
  &&  “ (StateLengthsPrefix states (Zlength (ops)) before_data_2 ) ” 
  &&  “ ((Zlength ((Znth c_pre states_2 __default__List_Z))) = (Zlength ((Znth (Zlength (ops)) states __default__List_Z)))) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < (Zlength (ops))) ” 
  &&  “ (BacktrackedPosition states (Znth z queries_data 0) (i - 1 ) ((((Znth i lefts 0) + k ) - (Znth (i - 0 ) before_data_2 0) ) - 1 ) ) ” 
  &&  “ (1 <= ((((Znth i lefts 0) + k ) - (Znth (i - 0 ) before_data_2 0) ) - 1 )) ” 
  &&  “ (((((Znth i lefts 0) + k ) - (Znth (i - 0 ) before_data_2 0) ) - 1 ) <= (200000 * (Z.pow (2) (40)) )) ”
  &&  emp
).

Definition solver_entail_wit_6_2 := 
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out_2: (@list Z)) (z: Z) (length: Z) (before_data_2: (@list Z)) (states_2: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k <= (Znth (i - 0 ) before_data_2 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states_2 )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states_2 c_pre before_data_2 )) (PreH19 : (length = (Zlength ((Znth c_pre states_2 __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out_2 )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states_2 (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data_2 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out_2 )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  EX (out: (@list Z))  (before_data: (@list Z))  (states: (@list (@list Z))) ,
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ (1 <= (Zlength (ops))) ” 
  &&  “ ((Zlength (ops)) <= 40) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 10000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (Pre text ops queries_data ) ” 
  &&  “ (CopyPasteStates text ops states ) ” 
  &&  “ (c_pre = (Zlength (ops))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ ((Zlength (lefts)) = c_pre) ” 
  &&  “ ((Zlength (rights)) = c_pre) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0)))) ” 
  &&  “ (StateLengthsPrefix states c_pre before_data ) ” 
  &&  “ (length = (Zlength ((Znth c_pre states __default__List_Z)))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < q_pre) ” 
  &&  “ (AnswerPrefix text ops queries_data z out ) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < c_pre) ” 
  &&  “ (BacktrackedPosition states (Znth z queries_data 0) (i - 1 ) k ) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= (200000 * (Z.pow (2) (40)) )) ”
  &&  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
) \/
(
forall (q_pre: Z) (c_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out_2: (@list Z)) (z: Z) (length: Z) (before_data_2: (@list Z)) (states_2: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k <= (Znth (i - 0 ) before_data_2 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states_2 )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states_2 c_pre before_data_2 )) (PreH19 : (length = (Zlength ((Znth c_pre states_2 __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out_2 )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states_2 (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  TT && emp 
|--
  EX (states: (@list (@list Z))) ,
  “ (CopyPasteStates text ops states ) ” 
  &&  “ (StateLengthsPrefix states (Zlength (ops)) before_data_2 ) ” 
  &&  “ ((Zlength ((Znth c_pre states_2 __default__List_Z))) = (Zlength ((Znth (Zlength (ops)) states __default__List_Z)))) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < (Zlength (ops))) ” 
  &&  “ (BacktrackedPosition states (Znth z queries_data 0) (i - 1 ) k ) ”
  &&  emp
).

Definition solver_entail_wit_7 := 
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (states_2: (@list (@list Z))) (before_data_2: (@list Z)) (out_2: (@list Z)) (length: Z) (z: Z) (k: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : (1 <= (Zlength (ops)))) (PreH5 : ((Zlength (ops)) <= 40)) (PreH6 : (1 <= (Zlength (queries_data)))) (PreH7 : ((Zlength (queries_data)) <= 10000)) (PreH8 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (Zlength (text)))) -> ((97 <= (Znth j_3 text 0)) /\ ((Znth j_3 text 0) <= 122)))) (PreH9 : (Pre text ops queries_data )) (PreH10 : (CopyPasteStates text ops states_2 )) (PreH11 : (c_pre = (Zlength (ops)))) (PreH12 : (q_pre = (Zlength (queries_data)))) (PreH13 : ((Zlength (lefts)) = c_pre)) (PreH14 : ((Zlength (rights)) = c_pre)) (PreH15 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < c_pre)) -> (((fst ((Znth j_4 ops __default__Prod_Z_Z))) = (Znth j_4 lefts 0)) /\ ((snd ((Znth j_4 ops __default__Prod_Z_Z))) = (Znth j_4 rights 0))))) (PreH16 : (StateLengthsPrefix states_2 c_pre before_data_2 )) (PreH17 : (length = (Zlength ((Znth c_pre states_2 __default__List_Z))))) (PreH18 : (0 <= z)) (PreH19 : (z < q_pre)) (PreH20 : (AnswerPrefix text ops queries_data z out_2 )) (PreH21 : (1 <= k)) (PreH22 : (k <= (Zlength (text)))) (PreH23 : (FinalCharacter text ops (Znth z queries_data 0) (Znth (k - 1 ) text 0) )) ,
  (CharArray.seg answers_pre 0 (z + 1 ) (app (out_2) ((cons ((Znth (k - 1 ) (c_string (text)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg answers_pre (z + 1 ) q_pre )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data_2 )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  EX (out: (@list Z))  (before_data: (@list Z))  (states: (@list (@list Z))) ,
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ (1 <= (Zlength (ops))) ” 
  &&  “ ((Zlength (ops)) <= 40) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 10000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (Pre text ops queries_data ) ” 
  &&  “ (CopyPasteStates text ops states ) ” 
  &&  “ (c_pre = (Zlength (ops))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ ((Zlength (lefts)) = c_pre) ” 
  &&  “ ((Zlength (rights)) = c_pre) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0)))) ” 
  &&  “ (StateLengthsPrefix states c_pre before_data ) ” 
  &&  “ (length = (Zlength ((Znth c_pre states __default__List_Z)))) ” 
  &&  “ (0 <= (z + 1 )) ” 
  &&  “ ((z + 1 ) <= q_pre) ” 
  &&  “ (AnswerPrefix text ops queries_data (z + 1 ) out ) ”
  &&  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 (z + 1 ) out )
  **  (CharArray.undef_seg answers_pre (z + 1 ) q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
) \/
(
forall (q_pre: Z) (c_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (states_2: (@list (@list Z))) (before_data_2: (@list Z)) (out_2: (@list Z)) (length: Z) (z: Z) (k: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : (1 <= (Zlength (ops)))) (PreH5 : ((Zlength (ops)) <= 40)) (PreH6 : (1 <= (Zlength (queries_data)))) (PreH7 : ((Zlength (queries_data)) <= 10000)) (PreH8 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (Zlength (text)))) -> ((97 <= (Znth j_3 text 0)) /\ ((Znth j_3 text 0) <= 122)))) (PreH9 : (Pre text ops queries_data )) (PreH10 : (CopyPasteStates text ops states_2 )) (PreH11 : (c_pre = (Zlength (ops)))) (PreH12 : (q_pre = (Zlength (queries_data)))) (PreH13 : ((Zlength (lefts)) = c_pre)) (PreH14 : ((Zlength (rights)) = c_pre)) (PreH15 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < c_pre)) -> (((fst ((Znth j_4 ops __default__Prod_Z_Z))) = (Znth j_4 lefts 0)) /\ ((snd ((Znth j_4 ops __default__Prod_Z_Z))) = (Znth j_4 rights 0))))) (PreH16 : (StateLengthsPrefix states_2 c_pre before_data_2 )) (PreH17 : (length = (Zlength ((Znth c_pre states_2 __default__List_Z))))) (PreH18 : (0 <= z)) (PreH19 : (z < q_pre)) (PreH20 : (AnswerPrefix text ops queries_data z out_2 )) (PreH21 : (1 <= k)) (PreH22 : (k <= (Zlength (text)))) (PreH23 : (FinalCharacter text ops (Znth z queries_data 0) (Znth (k - 1 ) text 0) )) ,
  TT && emp 
|--
  EX (states: (@list (@list Z))) ,
  “ (CopyPasteStates text ops states ) ” 
  &&  “ (StateLengthsPrefix states (Zlength (ops)) before_data_2 ) ” 
  &&  “ ((Zlength ((Znth c_pre states_2 __default__List_Z))) = (Zlength ((Znth (Zlength (ops)) states __default__List_Z)))) ” 
  &&  “ (0 <= (z + 1 )) ” 
  &&  “ ((z + 1 ) <= (Zlength (queries_data))) ” 
  &&  “ (AnswerPrefix text ops queries_data (z + 1 ) (app (out_2) ((cons ((Znth (k - 1 ) (c_string (text)) 0)) ((@nil Z))))) ) ”
  &&  emp
).

Definition solver_entail_wit_8 := 
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (out_2: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states_2: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (z >= q_pre)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : (1 <= (Zlength (ops)))) (PreH5 : ((Zlength (ops)) <= 40)) (PreH6 : (1 <= (Zlength (queries_data)))) (PreH7 : ((Zlength (queries_data)) <= 10000)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH9 : (Pre text ops queries_data )) (PreH10 : (CopyPasteStates text ops states_2 )) (PreH11 : (c_pre = (Zlength (ops)))) (PreH12 : (q_pre = (Zlength (queries_data)))) (PreH13 : ((Zlength (lefts)) = c_pre)) (PreH14 : ((Zlength (rights)) = c_pre)) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH16 : (StateLengthsPrefix states_2 c_pre before_data )) (PreH17 : (length = (Zlength ((Znth c_pre states_2 __default__List_Z))))) (PreH18 : (0 <= z)) (PreH19 : (z <= q_pre)) (PreH20 : (AnswerPrefix text ops queries_data z out_2 )) ,
  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out_2 )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  EX (out: (@list Z))  (states: (@list (@list Z))) ,
  “ (CopyPasteStates text ops states ) ” 
  &&  “ (length = (Zlength ((Znth c_pre states __default__List_Z)))) ” 
  &&  “ (Spec text ops queries_data out ) ”
  &&  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.full answers_pre q_pre out )
  **  (Int64Array.undef_full ( &( "before" ) ) 40 )
) \/
(
forall (answers_pre: Z) (q_pre: Z) (c_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (out_2: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states_2: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (z >= q_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states_2 )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (StateLengthsPrefix states_2 c_pre before_data )) (PreH18 : (length = (Zlength ((Znth c_pre states_2 __default__List_Z))))) (PreH19 : (0 <= z)) (PreH20 : (z <= q_pre)) (PreH21 : (AnswerPrefix text ops queries_data z out_2 )) ,
  (CharArray.seg answers_pre 0 z out_2 )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  EX (out: (@list Z))  (states: (@list (@list Z))) ,
  “ (CopyPasteStates text ops states ) ” 
  &&  “ (length = (Zlength ((Znth c_pre states __default__List_Z)))) ” 
  &&  “ (Spec text ops queries_data out ) ”
  &&  (CharArray.full answers_pre q_pre out )
  **  (Int64Array.undef_full ( &( "before" ) ) 40 )
).

Definition solver_return_wit_1 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (states: (@list (@list Z))) (out_2: (@list Z)) (length: Z)  __default__List_Z (PreH1 : (CopyPasteStates text ops states )) (PreH2 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH3 : (Spec text ops queries_data out_2 )) ,
  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.full answers_pre q_pre out_2 )
|--
  EX (out: (@list Z)) ,
  “ (Spec text ops queries_data out ) ”
  &&  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.full answers_pre q_pre out )
.

Definition solver_partial_solve_wit_1_pure := 
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z))  __default__Prod_Z_Z (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : (1 <= (Zlength (ops)))) (PreH4 : ((Zlength (ops)) <= 40)) (PreH5 : (1 <= (Zlength (queries_data)))) (PreH6 : ((Zlength (queries_data)) <= 10000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH8 : (Pre text ops queries_data )) (PreH9 : (c_pre = (Zlength (ops)))) (PreH10 : (q_pre = (Zlength (queries_data)))) (PreH11 : ((Zlength (lefts)) = c_pre)) (PreH12 : ((Zlength (rights)) = c_pre)) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < c_pre)) -> (((fst ((Znth i_2 ops __default__Prod_Z_Z))) = (Znth i_2 lefts 0)) /\ ((snd ((Znth i_2 ops __default__Prod_Z_Z))) = (Znth i_2 rights 0))))) ,
  ((( &( "length" ) )) # Int64  |->_)
  **  (Int64Array.undef_full ( &( "before" ) ) 40 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ ((string_length (text)) < INT_MAX) ” 
  &&  “ (valid_string text ) ”
) \/
(
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z))  __default__Prod_Z_Z (PreH1 : (q_pre <= INT_MAX)) (PreH2 : (c_pre <= INT_MAX)) (PreH3 : (q_pre >= INT_MIN)) (PreH4 : (c_pre >= INT_MIN)) (PreH5 : (0 <= ((string_length (text)) + 1 ))) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : (1 <= (Zlength (ops)))) (PreH9 : ((Zlength (ops)) <= 40)) (PreH10 : (1 <= (Zlength (queries_data)))) (PreH11 : ((Zlength (queries_data)) <= 10000)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH13 : (Pre text ops queries_data )) (PreH14 : (c_pre = (Zlength (ops)))) (PreH15 : (q_pre = (Zlength (queries_data)))) (PreH16 : ((Zlength (lefts)) = c_pre)) (PreH17 : ((Zlength (rights)) = c_pre)) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < c_pre)) -> (((fst ((Znth i_2 ops __default__Prod_Z_Z))) = (Znth i_2 lefts 0)) /\ ((snd ((Znth i_2 ops __default__Prod_Z_Z))) = (Znth i_2 rights 0))))) ,
  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "length" ) )) # Int64  |->_)
  **  (Int64Array.undef_full ( &( "before" ) ) 40 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ (valid_string text ) ” 
  &&  “ ((string_length (text)) < INT_MAX) ”
).

Definition solver_partial_solve_wit_1_pure_split_goal_1 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z))  __default__Prod_Z_Z (PreH1 : (q_pre <= INT_MAX)) (PreH2 : (c_pre <= INT_MAX)) (PreH3 : (q_pre >= INT_MIN)) (PreH4 : (c_pre >= INT_MIN)) (PreH5 : (0 <= ((string_length (text)) + 1 ))) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : (1 <= (Zlength (ops)))) (PreH9 : ((Zlength (ops)) <= 40)) (PreH10 : (1 <= (Zlength (queries_data)))) (PreH11 : ((Zlength (queries_data)) <= 10000)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH13 : (Pre text ops queries_data )) (PreH14 : (c_pre = (Zlength (ops)))) (PreH15 : (q_pre = (Zlength (queries_data)))) (PreH16 : ((Zlength (lefts)) = c_pre)) (PreH17 : ((Zlength (rights)) = c_pre)) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < c_pre)) -> (((fst ((Znth i_2 ops __default__Prod_Z_Z))) = (Znth i_2 lefts 0)) /\ ((snd ((Znth i_2 ops __default__Prod_Z_Z))) = (Znth i_2 rights 0))))) ,
  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "length" ) )) # Int64  |->_)
  **  (Int64Array.undef_full ( &( "before" ) ) 40 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ (valid_string text ) ”
.

Definition solver_partial_solve_wit_1_pure_split_goal_2 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z))  __default__Prod_Z_Z (PreH1 : (q_pre <= INT_MAX)) (PreH2 : (c_pre <= INT_MAX)) (PreH3 : (q_pre >= INT_MIN)) (PreH4 : (c_pre >= INT_MIN)) (PreH5 : (0 <= ((string_length (text)) + 1 ))) (PreH6 : (1 <= (Zlength (text)))) (PreH7 : ((Zlength (text)) <= 200000)) (PreH8 : (1 <= (Zlength (ops)))) (PreH9 : ((Zlength (ops)) <= 40)) (PreH10 : (1 <= (Zlength (queries_data)))) (PreH11 : ((Zlength (queries_data)) <= 10000)) (PreH12 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH13 : (Pre text ops queries_data )) (PreH14 : (c_pre = (Zlength (ops)))) (PreH15 : (q_pre = (Zlength (queries_data)))) (PreH16 : ((Zlength (lefts)) = c_pre)) (PreH17 : ((Zlength (rights)) = c_pre)) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < c_pre)) -> (((fst ((Znth i_2 ops __default__Prod_Z_Z))) = (Znth i_2 lefts 0)) /\ ((snd ((Znth i_2 ops __default__Prod_Z_Z))) = (Znth i_2 rights 0))))) ,
  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  ((( &( "length" ) )) # Int64  |->_)
  **  (Int64Array.undef_full ( &( "before" ) ) 40 )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "answers" ) )) # Ptr  |-> answers_pre)
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ ((string_length (text)) < INT_MAX) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z))  __default__Prod_Z_Z (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : (1 <= (Zlength (ops)))) (PreH4 : ((Zlength (ops)) <= 40)) (PreH5 : (1 <= (Zlength (queries_data)))) (PreH6 : ((Zlength (queries_data)) <= 10000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH8 : (Pre text ops queries_data )) (PreH9 : (c_pre = (Zlength (ops)))) (PreH10 : (q_pre = (Zlength (queries_data)))) (PreH11 : ((Zlength (lefts)) = c_pre)) (PreH12 : ((Zlength (rights)) = c_pre)) (PreH13 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < c_pre)) -> (((fst ((Znth i_2 ops __default__Prod_Z_Z))) = (Znth i_2 lefts 0)) /\ ((snd ((Znth i_2 ops __default__Prod_Z_Z))) = (Znth i_2 rights 0))))) ,
  (Int64Array.undef_full ( &( "before" ) ) 40 )
  **  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ ((string_length (text)) < INT_MAX) ” 
  &&  “ (valid_string text ) ” 
  &&  “ (0 <= ((string_length (text)) + 1 )) ” 
  &&  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ (1 <= (Zlength (ops))) ” 
  &&  “ ((Zlength (ops)) <= 40) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 10000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122))) ” 
  &&  “ (Pre text ops queries_data ) ” 
  &&  “ (c_pre = (Zlength (ops))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ ((Zlength (lefts)) = c_pre) ” 
  &&  “ ((Zlength (rights)) = c_pre) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < c_pre)) -> (((fst ((Znth i_2 ops __default__Prod_Z_Z))) = (Znth i_2 lefts 0)) /\ ((snd ((Znth i_2 ops __default__Prod_Z_Z))) = (Znth i_2 rights 0)))) ”
  &&  (store_string s_pre text )
  **  (Int64Array.undef_full ( &( "before" ) ) 40 )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data: (@list Z)) (length: Z) (i: Z) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i < c_pre)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : (1 <= (Zlength (ops)))) (PreH5 : ((Zlength (ops)) <= 40)) (PreH6 : (1 <= (Zlength (queries_data)))) (PreH7 : ((Zlength (queries_data)) <= 10000)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH9 : (Pre text ops queries_data )) (PreH10 : (CopyPasteStates text ops states )) (PreH11 : (c_pre = (Zlength (ops)))) (PreH12 : (q_pre = (Zlength (queries_data)))) (PreH13 : ((Zlength (lefts)) = c_pre)) (PreH14 : ((Zlength (rights)) = c_pre)) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH16 : (0 <= i)) (PreH17 : (i <= c_pre)) (PreH18 : (length = (Zlength ((Znth i states __default__List_Z))))) (PreH19 : (1 <= length)) (PreH20 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH21 : (StateLengthsPrefix states i before_data )) ,
  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 i before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) i 40 )
|--
  “ (0 <= ((string_length (text)) + 1 )) ” 
  &&  “ (i < c_pre) ” 
  &&  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ (1 <= (Zlength (ops))) ” 
  &&  “ ((Zlength (ops)) <= 40) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 10000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (Pre text ops queries_data ) ” 
  &&  “ (CopyPasteStates text ops states ) ” 
  &&  “ (c_pre = (Zlength (ops))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ ((Zlength (lefts)) = c_pre) ” 
  &&  “ ((Zlength (rights)) = c_pre) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= c_pre) ” 
  &&  “ (length = (Zlength ((Znth i states __default__List_Z)))) ” 
  &&  “ (1 <= length) ” 
  &&  “ (length <= (200000 * (Z.pow (2) (40)) )) ” 
  &&  “ (StateLengthsPrefix states i before_data ) ”
  &&  (((( &( "before" ) ) + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 i before_data )
.

Definition solver_partial_solve_wit_3 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data: (@list Z)) (length: Z) (i: Z) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (i < c_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (0 <= i)) (PreH18 : (i <= c_pre)) (PreH19 : (length = (Zlength ((Znth i states __default__List_Z))))) (PreH20 : (1 <= length)) (PreH21 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH22 : (StateLengthsPrefix states i before_data )) ,
  (Int64Array.seg ( &( "before" ) ) 0 (i + 1 ) (app (before_data) ((cons (length) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ (0 <= ((string_length (text)) + 1 )) ” 
  &&  “ (i < c_pre) ” 
  &&  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ (1 <= (Zlength (ops))) ” 
  &&  “ ((Zlength (ops)) <= 40) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 10000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (Pre text ops queries_data ) ” 
  &&  “ (CopyPasteStates text ops states ) ” 
  &&  “ (c_pre = (Zlength (ops))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ ((Zlength (lefts)) = c_pre) ” 
  &&  “ ((Zlength (rights)) = c_pre) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= c_pre) ” 
  &&  “ (length = (Zlength ((Znth i states __default__List_Z)))) ” 
  &&  “ (1 <= length) ” 
  &&  “ (length <= (200000 * (Z.pow (2) (40)) )) ” 
  &&  “ (StateLengthsPrefix states i before_data ) ”
  &&  (((r_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i rights 0))
  **  (Int64Array.missing_i r_pre i 0 c_pre rights )
  **  (Int64Array.seg ( &( "before" ) ) 0 (i + 1 ) (app (before_data) ((cons (length) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
.

Definition solver_partial_solve_wit_4 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (before_data: (@list Z)) (length: Z) (i: Z) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (0 <= ((string_length (text)) + 1 ))) (PreH2 : (i < c_pre)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : (1 <= (Zlength (ops)))) (PreH6 : ((Zlength (ops)) <= 40)) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 10000)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH10 : (Pre text ops queries_data )) (PreH11 : (CopyPasteStates text ops states )) (PreH12 : (c_pre = (Zlength (ops)))) (PreH13 : (q_pre = (Zlength (queries_data)))) (PreH14 : ((Zlength (lefts)) = c_pre)) (PreH15 : ((Zlength (rights)) = c_pre)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH17 : (0 <= i)) (PreH18 : (i <= c_pre)) (PreH19 : (length = (Zlength ((Znth i states __default__List_Z))))) (PreH20 : (1 <= length)) (PreH21 : (length <= (200000 * (Z.pow (2) (40)) ))) (PreH22 : (StateLengthsPrefix states i before_data )) ,
  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.seg ( &( "before" ) ) 0 (i + 1 ) (app (before_data) ((cons (length) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
|--
  “ (0 <= ((string_length (text)) + 1 )) ” 
  &&  “ (i < c_pre) ” 
  &&  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ (1 <= (Zlength (ops))) ” 
  &&  “ ((Zlength (ops)) <= 40) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 10000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (Pre text ops queries_data ) ” 
  &&  “ (CopyPasteStates text ops states ) ” 
  &&  “ (c_pre = (Zlength (ops))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ ((Zlength (lefts)) = c_pre) ” 
  &&  “ ((Zlength (rights)) = c_pre) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= c_pre) ” 
  &&  “ (length = (Zlength ((Znth i states __default__List_Z)))) ” 
  &&  “ (1 <= length) ” 
  &&  “ (length <= (200000 * (Z.pow (2) (40)) )) ” 
  &&  “ (StateLengthsPrefix states i before_data ) ”
  &&  (((l_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i lefts 0))
  **  (Int64Array.missing_i l_pre i 0 c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.seg ( &( "before" ) ) 0 (i + 1 ) (app (before_data) ((cons (length) ((@nil Z))))) )
  **  (Int64Array.undef_seg ( &( "before" ) ) (i + 1 ) 40 )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.undef_full answers_pre q_pre )
.

Definition solver_partial_solve_wit_5 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (z < q_pre)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : (1 <= (Zlength (ops)))) (PreH5 : ((Zlength (ops)) <= 40)) (PreH6 : (1 <= (Zlength (queries_data)))) (PreH7 : ((Zlength (queries_data)) <= 10000)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH9 : (Pre text ops queries_data )) (PreH10 : (CopyPasteStates text ops states )) (PreH11 : (c_pre = (Zlength (ops)))) (PreH12 : (q_pre = (Zlength (queries_data)))) (PreH13 : ((Zlength (lefts)) = c_pre)) (PreH14 : ((Zlength (rights)) = c_pre)) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH16 : (StateLengthsPrefix states c_pre before_data )) (PreH17 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH18 : (0 <= z)) (PreH19 : (z <= q_pre)) (PreH20 : (AnswerPrefix text ops queries_data z out )) ,
  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ (0 <= ((string_length (text)) + 1 )) ” 
  &&  “ (z < q_pre) ” 
  &&  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ (1 <= (Zlength (ops))) ” 
  &&  “ ((Zlength (ops)) <= 40) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 10000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (Pre text ops queries_data ) ” 
  &&  “ (CopyPasteStates text ops states ) ” 
  &&  “ (c_pre = (Zlength (ops))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ ((Zlength (lefts)) = c_pre) ” 
  &&  “ ((Zlength (rights)) = c_pre) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0)))) ” 
  &&  “ (StateLengthsPrefix states c_pre before_data ) ” 
  &&  “ (length = (Zlength ((Znth c_pre states __default__List_Z)))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z <= q_pre) ” 
  &&  “ (AnswerPrefix text ops queries_data z out ) ”
  &&  (((queries_pre + (z * sizeof(INT64)))) # Int64  |-> (Znth z queries_data 0))
  **  (Int64Array.missing_i queries_pre z 0 q_pre queries_data )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
.

Definition solver_partial_solve_wit_6 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (i >= 0)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : (1 <= (Zlength (ops)))) (PreH5 : ((Zlength (ops)) <= 40)) (PreH6 : (1 <= (Zlength (queries_data)))) (PreH7 : ((Zlength (queries_data)) <= 10000)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH9 : (Pre text ops queries_data )) (PreH10 : (CopyPasteStates text ops states )) (PreH11 : (c_pre = (Zlength (ops)))) (PreH12 : (q_pre = (Zlength (queries_data)))) (PreH13 : ((Zlength (lefts)) = c_pre)) (PreH14 : ((Zlength (rights)) = c_pre)) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH16 : (StateLengthsPrefix states c_pre before_data )) (PreH17 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH18 : (0 <= z)) (PreH19 : (z < q_pre)) (PreH20 : (AnswerPrefix text ops queries_data z out )) (PreH21 : ((-1) <= i)) (PreH22 : (i < c_pre)) (PreH23 : (BacktrackedPosition states (Znth z queries_data 0) i k )) (PreH24 : (1 <= k)) (PreH25 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ (0 <= ((string_length (text)) + 1 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ (1 <= (Zlength (ops))) ” 
  &&  “ ((Zlength (ops)) <= 40) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 10000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (Pre text ops queries_data ) ” 
  &&  “ (CopyPasteStates text ops states ) ” 
  &&  “ (c_pre = (Zlength (ops))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ ((Zlength (lefts)) = c_pre) ” 
  &&  “ ((Zlength (rights)) = c_pre) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0)))) ” 
  &&  “ (StateLengthsPrefix states c_pre before_data ) ” 
  &&  “ (length = (Zlength ((Znth c_pre states __default__List_Z)))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < q_pre) ” 
  &&  “ (AnswerPrefix text ops queries_data z out ) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < c_pre) ” 
  &&  “ (BacktrackedPosition states (Znth z queries_data 0) i k ) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= (200000 * (Z.pow (2) (40)) )) ”
  &&  (((( &( "before" ) ) + (i * sizeof(INT64)))) # Int64  |-> (Znth (i - 0 ) before_data 0))
  **  (Int64Array.missing_i ( &( "before" ) ) i 0 c_pre before_data )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
.

Definition solver_partial_solve_wit_7 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k > (Znth (i - 0 ) before_data 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states c_pre before_data )) (PreH19 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ (k > (Znth (i - 0 ) before_data 0)) ” 
  &&  “ (0 <= ((string_length (text)) + 1 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ (1 <= (Zlength (ops))) ” 
  &&  “ ((Zlength (ops)) <= 40) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 10000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (Pre text ops queries_data ) ” 
  &&  “ (CopyPasteStates text ops states ) ” 
  &&  “ (c_pre = (Zlength (ops))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ ((Zlength (lefts)) = c_pre) ” 
  &&  “ ((Zlength (rights)) = c_pre) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0)))) ” 
  &&  “ (StateLengthsPrefix states c_pre before_data ) ” 
  &&  “ (length = (Zlength ((Znth c_pre states __default__List_Z)))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < q_pre) ” 
  &&  “ (AnswerPrefix text ops queries_data z out ) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < c_pre) ” 
  &&  “ (BacktrackedPosition states (Znth z queries_data 0) i k ) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= (200000 * (Z.pow (2) (40)) )) ”
  &&  (((l_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i lefts 0))
  **  (Int64Array.missing_i l_pre i 0 c_pre lefts )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
.

Definition solver_partial_solve_wit_8 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (k: Z) (i: Z) (out: (@list Z)) (z: Z) (length: Z) (before_data: (@list Z)) (states: (@list (@list Z)))  __default__List_Z  __default__Prod_Z_Z (PreH1 : (k > (Znth (i - 0 ) before_data 0))) (PreH2 : (0 <= ((string_length (text)) + 1 ))) (PreH3 : (i >= 0)) (PreH4 : (1 <= (Zlength (text)))) (PreH5 : ((Zlength (text)) <= 200000)) (PreH6 : (1 <= (Zlength (ops)))) (PreH7 : ((Zlength (ops)) <= 40)) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 10000)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH11 : (Pre text ops queries_data )) (PreH12 : (CopyPasteStates text ops states )) (PreH13 : (c_pre = (Zlength (ops)))) (PreH14 : (q_pre = (Zlength (queries_data)))) (PreH15 : ((Zlength (lefts)) = c_pre)) (PreH16 : ((Zlength (rights)) = c_pre)) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH18 : (StateLengthsPrefix states c_pre before_data )) (PreH19 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH20 : (0 <= z)) (PreH21 : (z < q_pre)) (PreH22 : (AnswerPrefix text ops queries_data z out )) (PreH23 : ((-1) <= i)) (PreH24 : (i < c_pre)) (PreH25 : (BacktrackedPosition states (Znth z queries_data 0) i k )) (PreH26 : (1 <= k)) (PreH27 : (k <= (200000 * (Z.pow (2) (40)) ))) ,
  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ (k > (Znth (i - 0 ) before_data 0)) ” 
  &&  “ (0 <= ((string_length (text)) + 1 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ (1 <= (Zlength (ops))) ” 
  &&  “ ((Zlength (ops)) <= 40) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 10000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (Pre text ops queries_data ) ” 
  &&  “ (CopyPasteStates text ops states ) ” 
  &&  “ (c_pre = (Zlength (ops))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ ((Zlength (lefts)) = c_pre) ” 
  &&  “ ((Zlength (rights)) = c_pre) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0)))) ” 
  &&  “ (StateLengthsPrefix states c_pre before_data ) ” 
  &&  “ (length = (Zlength ((Znth c_pre states __default__List_Z)))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < q_pre) ” 
  &&  “ (AnswerPrefix text ops queries_data z out ) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < c_pre) ” 
  &&  “ (BacktrackedPosition states (Znth z queries_data 0) i k ) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= (200000 * (Z.pow (2) (40)) )) ”
  &&  (((( &( "before" ) ) + (i * sizeof(INT64)))) # Int64  |-> (Znth (i - 0 ) before_data 0))
  **  (Int64Array.missing_i ( &( "before" ) ) i 0 c_pre before_data )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
.

Definition solver_partial_solve_wit_9 := 
forall (answers_pre: Z) (queries_pre: Z) (q_pre: Z) (r_pre: Z) (l_pre: Z) (c_pre: Z) (s_pre: Z) (rights: (@list Z)) (lefts: (@list Z)) (queries_data: (@list Z)) (ops: (@list (Z * Z))) (text: (@list Z)) (states: (@list (@list Z))) (before_data: (@list Z)) (out: (@list Z)) (length: Z) (z: Z) (k: Z)  __default__List_Z  __default__Prod_Z_Z (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : (1 <= (Zlength (ops)))) (PreH4 : ((Zlength (ops)) <= 40)) (PreH5 : (1 <= (Zlength (queries_data)))) (PreH6 : ((Zlength (queries_data)) <= 10000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH8 : (Pre text ops queries_data )) (PreH9 : (CopyPasteStates text ops states )) (PreH10 : (c_pre = (Zlength (ops)))) (PreH11 : (q_pre = (Zlength (queries_data)))) (PreH12 : ((Zlength (lefts)) = c_pre)) (PreH13 : ((Zlength (rights)) = c_pre)) (PreH14 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0))))) (PreH15 : (StateLengthsPrefix states c_pre before_data )) (PreH16 : (length = (Zlength ((Znth c_pre states __default__List_Z))))) (PreH17 : (0 <= z)) (PreH18 : (z < q_pre)) (PreH19 : (AnswerPrefix text ops queries_data z out )) (PreH20 : (1 <= k)) (PreH21 : (k <= (Zlength (text)))) (PreH22 : (FinalCharacter text ops (Znth z queries_data 0) (Znth (k - 1 ) text 0) )) ,
  (store_string s_pre text )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (CharArray.undef_seg answers_pre z q_pre )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
|--
  “ (0 <= ((string_length (text)) + 1 )) ” 
  &&  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ (1 <= (Zlength (ops))) ” 
  &&  “ ((Zlength (ops)) <= 40) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 10000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (Pre text ops queries_data ) ” 
  &&  “ (CopyPasteStates text ops states ) ” 
  &&  “ (c_pre = (Zlength (ops))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ ((Zlength (lefts)) = c_pre) ” 
  &&  “ ((Zlength (rights)) = c_pre) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < c_pre)) -> (((fst ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 lefts 0)) /\ ((snd ((Znth j_2 ops __default__Prod_Z_Z))) = (Znth j_2 rights 0)))) ” 
  &&  “ (StateLengthsPrefix states c_pre before_data ) ” 
  &&  “ (length = (Zlength ((Znth c_pre states __default__List_Z)))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < q_pre) ” 
  &&  “ (AnswerPrefix text ops queries_data z out ) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= (Zlength (text))) ” 
  &&  “ (FinalCharacter text ops (Znth z queries_data 0) (Znth (k - 1 ) text 0) ) ”
  &&  (((answers_pre + (z * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (text)) + 1 ) (c_string (text)) )
  **  (CharArray.undef_missing_i answers_pre z z q_pre )
  **  (Int64Array.full l_pre c_pre lefts )
  **  (Int64Array.full r_pre c_pre rights )
  **  (Int64Array.full queries_pre q_pre queries_data )
  **  (CharArray.seg answers_pre 0 z out )
  **  (Int64Array.seg ( &( "before" ) ) 0 c_pre before_data )
  **  (Int64Array.undef_seg ( &( "before" ) ) c_pre 40 )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Axiom proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.

End VC_Correct.
