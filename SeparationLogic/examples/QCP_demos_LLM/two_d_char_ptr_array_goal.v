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
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.

(*----- Function check_dict_case -----*)

Definition check_dict_case_safety_wit_1 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (PreH1 : (0 <= dict_size_pre)) (PreH2 : (dict_size_pre <= 100)) (PreH3 : ((Zlength (rows)) = dict_size_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < dict_size_pre)) -> (((0 < (Zlength ((Znth (k) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (k) (rows) ((@nil Z))))) - 1 )) ((Znth (k) (rows) ((@nil Z)))) (0)) = 0)))) (PreH5 : forall (k_2: Z) , forall (i: Z) , (((((0 <= k_2) /\ (k_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (k_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (k_2) (rows) ((@nil Z)))) (0)) <> 0))) ,
  ((( &( "isupper" ) )) # Int  |->_)
  **  ((( &( "islower" ) )) # Int  |-> 0)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_2 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (PreH1 : (0 <= dict_size_pre)) (PreH2 : (dict_size_pre <= 100)) (PreH3 : ((Zlength (rows)) = dict_size_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < dict_size_pre)) -> (((0 < (Zlength ((Znth (k) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (k) (rows) ((@nil Z))))) - 1 )) ((Znth (k) (rows) ((@nil Z)))) (0)) = 0)))) (PreH5 : forall (k_2: Z) , forall (i: Z) , (((((0 <= k_2) /\ (k_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (k_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (k_2) (rows) ((@nil Z)))) (0)) <> 0))) ,
  ((( &( "islower" ) )) # Int  |->_)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_3 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (PreH1 : (0 <= dict_size_pre)) (PreH2 : (dict_size_pre <= 100)) (PreH3 : ((Zlength (rows)) = dict_size_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < dict_size_pre)) -> (((0 < (Zlength ((Znth (k) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (k) (rows) ((@nil Z))))) - 1 )) ((Znth (k) (rows) ((@nil Z)))) (0)) = 0)))) (PreH5 : forall (k_2: Z) , forall (i: Z) , (((((0 <= k_2) /\ (k_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (k_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (k_2) (rows) ((@nil Z)))) (0)) <> 0))) ,
  ((( &( "isupper" ) )) # Int  |-> 0)
  **  ((( &( "islower" ) )) # Int  |-> 0)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_4 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (PreH1 : (dict_size_pre = 0)) (PreH2 : (0 <= dict_size_pre)) (PreH3 : (dict_size_pre <= 100)) (PreH4 : ((Zlength (rows)) = dict_size_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < dict_size_pre)) -> (((0 < (Zlength ((Znth (k) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (k) (rows) ((@nil Z))))) - 1 )) ((Znth (k) (rows) ((@nil Z)))) (0)) = 0)))) (PreH6 : forall (k_2: Z) , forall (i: Z) , (((((0 <= k_2) /\ (k_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (k_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (k_2) (rows) ((@nil Z)))) (0)) <> 0))) ,
  ((( &( "isupper" ) )) # Int  |-> 0)
  **  ((( &( "islower" ) )) # Int  |-> 0)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_5 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (PreH1 : (dict_size_pre <> 0)) (PreH2 : (0 <= dict_size_pre)) (PreH3 : (dict_size_pre <= 100)) (PreH4 : ((Zlength (rows)) = dict_size_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < dict_size_pre)) -> (((0 < (Zlength ((Znth (k) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (k) (rows) ((@nil Z))))) - 1 )) ((Znth (k) (rows) ((@nil Z)))) (0)) = 0)))) (PreH6 : forall (k_2: Z) , forall (i: Z) , (((((0 <= k_2) /\ (k_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (k_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (k_2) (rows) ((@nil Z)))) (0)) <> 0))) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "isupper" ) )) # Int  |-> 0)
  **  ((( &( "islower" ) )) # Int  |-> 0)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_6 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (k: Z) (islower: Z) (isupper: Z) (PreH1 : (0 <= k)) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 <= dict_size_pre)) (PreH4 : (dict_size_pre <= 100)) (PreH5 : ((Zlength (rows)) = dict_size_pre)) (PreH6 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH7 : forall (r_2: Z) , forall (i: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH8 : (0 <= islower)) (PreH9 : (islower <= 1)) (PreH10 : (0 <= isupper)) (PreH11 : (isupper <= 1)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_7 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH3 : (0 <= k)) (PreH4 : (k < dict_size_pre)) (PreH5 : (0 <= dict_size_pre)) (PreH6 : (dict_size_pre <= 100)) (PreH7 : ((Zlength (rows)) = dict_size_pre)) (PreH8 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH9 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH10 : (0 <= islower)) (PreH11 : (islower <= 1)) (PreH12 : (0 <= isupper)) (PreH13 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_8 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH2 : (0 <= i)) (PreH3 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH4 : (0 <= k)) (PreH5 : (k < dict_size_pre)) (PreH6 : (0 <= dict_size_pre)) (PreH7 : (dict_size_pre <= 100)) (PreH8 : ((Zlength (rows)) = dict_size_pre)) (PreH9 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH10 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH11 : (0 <= islower)) (PreH12 : (islower <= 1)) (PreH13 : (0 <= isupper)) (PreH14 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition check_dict_case_safety_wit_9 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH3 : (0 <= i)) (PreH4 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH5 : (0 <= k)) (PreH6 : (k < dict_size_pre)) (PreH7 : (0 <= dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : ((Zlength (rows)) = dict_size_pre)) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH11 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH12 : (0 <= islower)) (PreH13 : (islower <= 1)) (PreH14 : (0 <= isupper)) (PreH15 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (90 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 90) ”
.

Definition check_dict_case_safety_wit_10 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH4 : (0 <= i)) (PreH5 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH6 : (0 <= k)) (PreH7 : (k < dict_size_pre)) (PreH8 : (0 <= dict_size_pre)) (PreH9 : (dict_size_pre <= 100)) (PreH10 : ((Zlength (rows)) = dict_size_pre)) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH12 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH13 : (0 <= islower)) (PreH14 : (islower <= 1)) (PreH15 : (0 <= isupper)) (PreH16 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition check_dict_case_safety_wit_11 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH4 : (0 <= i)) (PreH5 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH6 : (0 <= k)) (PreH7 : (k < dict_size_pre)) (PreH8 : (0 <= dict_size_pre)) (PreH9 : (dict_size_pre <= 100)) (PreH10 : ((Zlength (rows)) = dict_size_pre)) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH12 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH13 : (0 <= islower)) (PreH14 : (islower <= 1)) (PreH15 : (0 <= isupper)) (PreH16 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (122 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 122) ”
.

Definition check_dict_case_safety_wit_12 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH7 : (0 <= k)) (PreH8 : (k < dict_size_pre)) (PreH9 : (0 <= dict_size_pre)) (PreH10 : (dict_size_pre <= 100)) (PreH11 : ((Zlength (rows)) = dict_size_pre)) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH13 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH14 : (0 <= islower)) (PreH15 : (islower <= 1)) (PreH16 : (0 <= isupper)) (PreH17 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (122 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 122) ”
.

Definition check_dict_case_safety_wit_13 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH7 : (0 <= k)) (PreH8 : (k < dict_size_pre)) (PreH9 : (0 <= dict_size_pre)) (PreH10 : (dict_size_pre <= 100)) (PreH11 : ((Zlength (rows)) = dict_size_pre)) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH13 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH14 : (0 <= islower)) (PreH15 : (islower <= 1)) (PreH16 : (0 <= isupper)) (PreH17 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ False ”
.

Definition check_dict_case_safety_wit_14 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH7 : (0 <= k)) (PreH8 : (k < dict_size_pre)) (PreH9 : (0 <= dict_size_pre)) (PreH10 : (dict_size_pre <= 100)) (PreH11 : ((Zlength (rows)) = dict_size_pre)) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH13 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH14 : (0 <= islower)) (PreH15 : (islower <= 1)) (PreH16 : (0 <= isupper)) (PreH17 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_15 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 65)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH3 : (0 <= i)) (PreH4 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH5 : (0 <= k)) (PreH6 : (k < dict_size_pre)) (PreH7 : (0 <= dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : ((Zlength (rows)) = dict_size_pre)) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH11 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH12 : (0 <= islower)) (PreH13 : (islower <= 1)) (PreH14 : (0 <= isupper)) (PreH15 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_16 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH8 : (0 <= k)) (PreH9 : (k < dict_size_pre)) (PreH10 : (0 <= dict_size_pre)) (PreH11 : (dict_size_pre <= 100)) (PreH12 : ((Zlength (rows)) = dict_size_pre)) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH14 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH15 : (0 <= islower)) (PreH16 : (islower <= 1)) (PreH17 : (0 <= isupper)) (PreH18 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_17 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH8 : (0 <= k)) (PreH9 : (k < dict_size_pre)) (PreH10 : (0 <= dict_size_pre)) (PreH11 : (dict_size_pre <= 100)) (PreH12 : ((Zlength (rows)) = dict_size_pre)) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH14 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH15 : (0 <= islower)) (PreH16 : (islower <= 1)) (PreH17 : (0 <= isupper)) (PreH18 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition check_dict_case_safety_wit_18 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH7 : (0 <= k)) (PreH8 : (k < dict_size_pre)) (PreH9 : (0 <= dict_size_pre)) (PreH10 : (dict_size_pre <= 100)) (PreH11 : ((Zlength (rows)) = dict_size_pre)) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH13 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH14 : (0 <= islower)) (PreH15 : (islower <= 1)) (PreH16 : (0 <= isupper)) (PreH17 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition check_dict_case_safety_wit_19 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 65)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH9 : (0 <= k)) (PreH10 : (k < dict_size_pre)) (PreH11 : (0 <= dict_size_pre)) (PreH12 : (dict_size_pre <= 100)) (PreH13 : ((Zlength (rows)) = dict_size_pre)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH15 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH16 : (0 <= islower)) (PreH17 : (islower <= 1)) (PreH18 : (0 <= isupper)) (PreH19 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ False ”
.

Definition check_dict_case_safety_wit_20 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 65)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH8 : (0 <= k)) (PreH9 : (k < dict_size_pre)) (PreH10 : (0 <= dict_size_pre)) (PreH11 : (dict_size_pre <= 100)) (PreH12 : ((Zlength (rows)) = dict_size_pre)) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH14 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH15 : (0 <= islower)) (PreH16 : (islower <= 1)) (PreH17 : (0 <= isupper)) (PreH18 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ False ”
.

Definition check_dict_case_safety_wit_21 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH8 : (0 <= k)) (PreH9 : (k < dict_size_pre)) (PreH10 : (0 <= dict_size_pre)) (PreH11 : (dict_size_pre <= 100)) (PreH12 : ((Zlength (rows)) = dict_size_pre)) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH14 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH15 : (0 <= islower)) (PreH16 : (islower <= 1)) (PreH17 : (0 <= isupper)) (PreH18 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (90 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 90) ”
.

Definition check_dict_case_safety_wit_22 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH9 : (0 <= k)) (PreH10 : (k < dict_size_pre)) (PreH11 : (0 <= dict_size_pre)) (PreH12 : (dict_size_pre <= 100)) (PreH13 : ((Zlength (rows)) = dict_size_pre)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH15 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH16 : (0 <= islower)) (PreH17 : (islower <= 1)) (PreH18 : (0 <= isupper)) (PreH19 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (90 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 90) ”
.

Definition check_dict_case_safety_wit_23 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH9 : (0 <= k)) (PreH10 : (k < dict_size_pre)) (PreH11 : (0 <= dict_size_pre)) (PreH12 : (dict_size_pre <= 100)) (PreH13 : ((Zlength (rows)) = dict_size_pre)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH15 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH16 : (0 <= islower)) (PreH17 : (islower <= 1)) (PreH18 : (0 <= isupper)) (PreH19 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ False ”
.

Definition check_dict_case_safety_wit_24 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH10 : (0 <= k)) (PreH11 : (k < dict_size_pre)) (PreH12 : (0 <= dict_size_pre)) (PreH13 : (dict_size_pre <= 100)) (PreH14 : ((Zlength (rows)) = dict_size_pre)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH16 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH17 : (0 <= islower)) (PreH18 : (islower <= 1)) (PreH19 : (0 <= isupper)) (PreH20 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ False ”
.

Definition check_dict_case_safety_wit_25 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH9 : (0 <= k)) (PreH10 : (k < dict_size_pre)) (PreH11 : (0 <= dict_size_pre)) (PreH12 : (dict_size_pre <= 100)) (PreH13 : ((Zlength (rows)) = dict_size_pre)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH15 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH16 : (0 <= islower)) (PreH17 : (islower <= 1)) (PreH18 : (0 <= isupper)) (PreH19 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_dict_case_safety_wit_26 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH9 : (0 <= k)) (PreH10 : (k < dict_size_pre)) (PreH11 : (0 <= dict_size_pre)) (PreH12 : (dict_size_pre <= 100)) (PreH13 : ((Zlength (rows)) = dict_size_pre)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH15 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH16 : (0 <= islower)) (PreH17 : (islower <= 1)) (PreH18 : (0 <= isupper)) (PreH19 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition check_dict_case_safety_wit_27 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH10 : (0 <= k)) (PreH11 : (k < dict_size_pre)) (PreH12 : (0 <= dict_size_pre)) (PreH13 : (dict_size_pre <= 100)) (PreH14 : ((Zlength (rows)) = dict_size_pre)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH16 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH17 : (0 <= islower)) (PreH18 : (islower <= 1)) (PreH19 : (0 <= isupper)) (PreH20 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition check_dict_case_safety_wit_28 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH10 : (0 <= k)) (PreH11 : (k < dict_size_pre)) (PreH12 : (0 <= dict_size_pre)) (PreH13 : (dict_size_pre <= 100)) (PreH14 : ((Zlength (rows)) = dict_size_pre)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH16 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH17 : (0 <= islower)) (PreH18 : (islower <= 1)) (PreH19 : (0 <= isupper)) (PreH20 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ False ”
.

Definition check_dict_case_safety_wit_29 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 <= dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : ((Zlength (rows)) = dict_size_pre)) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH17 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH18 : (0 <= islower)) (PreH19 : (islower <= 1)) (PreH20 : (0 <= isupper)) (PreH21 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ False ”
.

Definition check_dict_case_safety_wit_30 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 <= dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : ((Zlength (rows)) = dict_size_pre)) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH17 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH18 : (0 <= islower)) (PreH19 : (islower <= 1)) (PreH20 : (0 <= isupper)) (PreH21 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (122 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 122) ”
.

Definition check_dict_case_safety_wit_31 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH12 : (0 <= k)) (PreH13 : (k < dict_size_pre)) (PreH14 : (0 <= dict_size_pre)) (PreH15 : (dict_size_pre <= 100)) (PreH16 : ((Zlength (rows)) = dict_size_pre)) (PreH17 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH18 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH19 : (0 <= islower)) (PreH20 : (islower <= 1)) (PreH21 : (0 <= isupper)) (PreH22 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ False ”
.

Definition check_dict_case_safety_wit_32 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH12 : (0 <= k)) (PreH13 : (k < dict_size_pre)) (PreH14 : (0 <= dict_size_pre)) (PreH15 : (dict_size_pre <= 100)) (PreH16 : ((Zlength (rows)) = dict_size_pre)) (PreH17 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH18 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH19 : (0 <= islower)) (PreH20 : (islower <= 1)) (PreH21 : (0 <= isupper)) (PreH22 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_dict_case_safety_wit_33 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH10 : (0 <= k)) (PreH11 : (k < dict_size_pre)) (PreH12 : (0 <= dict_size_pre)) (PreH13 : (dict_size_pre <= 100)) (PreH14 : ((Zlength (rows)) = dict_size_pre)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH16 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH17 : (0 <= islower)) (PreH18 : (islower <= 1)) (PreH19 : (0 <= isupper)) (PreH20 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((1 + islower ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (1 + islower )) ”
.

Definition check_dict_case_safety_wit_34 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH12 : (0 <= k)) (PreH13 : (k < dict_size_pre)) (PreH14 : (0 <= dict_size_pre)) (PreH15 : (dict_size_pre <= 100)) (PreH16 : ((Zlength (rows)) = dict_size_pre)) (PreH17 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH18 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH19 : (0 <= islower)) (PreH20 : (islower <= 1)) (PreH21 : (0 <= isupper)) (PreH22 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> 1)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((isupper + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (isupper + 1 )) ”
.

Definition check_dict_case_safety_wit_35 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH12 : (0 <= k)) (PreH13 : (k < dict_size_pre)) (PreH14 : (0 <= dict_size_pre)) (PreH15 : (dict_size_pre <= 100)) (PreH16 : ((Zlength (rows)) = dict_size_pre)) (PreH17 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH18 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH19 : (0 <= islower)) (PreH20 : (islower <= 1)) (PreH21 : (0 <= isupper)) (PreH22 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> 1)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition check_dict_case_safety_wit_36 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH10 : (0 <= k)) (PreH11 : (k < dict_size_pre)) (PreH12 : (0 <= dict_size_pre)) (PreH13 : (dict_size_pre <= 100)) (PreH14 : ((Zlength (rows)) = dict_size_pre)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH16 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH17 : (0 <= islower)) (PreH18 : (islower <= 1)) (PreH19 : (0 <= isupper)) (PreH20 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition check_dict_case_safety_wit_37 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((isupper + 1 ) = 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH13 : (0 <= k)) (PreH14 : (k < dict_size_pre)) (PreH15 : (0 <= dict_size_pre)) (PreH16 : (dict_size_pre <= 100)) (PreH17 : ((Zlength (rows)) = dict_size_pre)) (PreH18 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH19 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH20 : (0 <= islower)) (PreH21 : (islower <= 1)) (PreH22 : (0 <= isupper)) (PreH23 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> 1)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_38 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((1 + islower ) = 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 <= dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : ((Zlength (rows)) = dict_size_pre)) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH17 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH18 : (0 <= islower)) (PreH19 : (islower <= 1)) (PreH20 : (0 <= isupper)) (PreH21 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition check_dict_case_safety_wit_39 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((isupper + 1 ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH13 : (0 <= k)) (PreH14 : (k < dict_size_pre)) (PreH15 : (0 <= dict_size_pre)) (PreH16 : (dict_size_pre <= 100)) (PreH17 : ((Zlength (rows)) = dict_size_pre)) (PreH18 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH19 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH20 : (0 <= islower)) (PreH21 : (islower <= 1)) (PreH22 : (0 <= isupper)) (PreH23 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> 1)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((isupper + 1 ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH13 : (0 <= k)) (PreH14 : (k < dict_size_pre)) (PreH15 : (0 <= dict_size_pre)) (PreH16 : (dict_size_pre <= 100)) (PreH17 : ((Zlength (rows)) = dict_size_pre)) (PreH18 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH19 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH20 : (0 <= islower)) (PreH21 : (islower <= 1)) (PreH22 : (0 <= isupper)) (PreH23 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> 1)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition check_dict_case_safety_wit_39_split_goal_1 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((isupper + 1 ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH13 : (0 <= k)) (PreH14 : (k < dict_size_pre)) (PreH15 : (0 <= dict_size_pre)) (PreH16 : (dict_size_pre <= 100)) (PreH17 : ((Zlength (rows)) = dict_size_pre)) (PreH18 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH19 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH20 : (0 <= islower)) (PreH21 : (islower <= 1)) (PreH22 : (0 <= isupper)) (PreH23 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> 1)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition check_dict_case_safety_wit_39_split_goal_2 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((isupper + 1 ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH13 : (0 <= k)) (PreH14 : (k < dict_size_pre)) (PreH15 : (0 <= dict_size_pre)) (PreH16 : (dict_size_pre <= 100)) (PreH17 : ((Zlength (rows)) = dict_size_pre)) (PreH18 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH19 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH20 : (0 <= islower)) (PreH21 : (islower <= 1)) (PreH22 : (0 <= isupper)) (PreH23 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> 1)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition check_dict_case_safety_wit_40 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((1 + islower ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 <= dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : ((Zlength (rows)) = dict_size_pre)) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH17 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH18 : (0 <= islower)) (PreH19 : (islower <= 1)) (PreH20 : (0 <= isupper)) (PreH21 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((1 + islower ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 <= dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : ((Zlength (rows)) = dict_size_pre)) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH17 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH18 : (0 <= islower)) (PreH19 : (islower <= 1)) (PreH20 : (0 <= isupper)) (PreH21 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition check_dict_case_safety_wit_40_split_goal_1 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((1 + islower ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 <= dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : ((Zlength (rows)) = dict_size_pre)) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH17 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH18 : (0 <= islower)) (PreH19 : (islower <= 1)) (PreH20 : (0 <= isupper)) (PreH21 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition check_dict_case_safety_wit_40_split_goal_2 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((1 + islower ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 <= dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : ((Zlength (rows)) = dict_size_pre)) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH17 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH18 : (0 <= islower)) (PreH19 : (islower <= 1)) (PreH20 : (0 <= isupper)) (PreH21 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "key" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> 1)
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition check_dict_case_safety_wit_41 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (k: Z) (islower: Z) (isupper: Z) (PreH1 : (0 <= k)) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 <= islower)) (PreH4 : (islower <= 1)) (PreH5 : (0 <= isupper)) (PreH6 : (isupper <= 1)) (PreH7 : (0 <= dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : ((Zlength (rows)) = dict_size_pre)) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH11 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) ,
  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition check_dict_case_safety_wit_42 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (k: Z) (PreH1 : (k >= dict_size_pre)) (PreH2 : (0 <= k)) (PreH3 : (k <= dict_size_pre)) (PreH4 : (0 <= dict_size_pre)) (PreH5 : (dict_size_pre <= 100)) (PreH6 : ((Zlength (rows)) = dict_size_pre)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH8 : forall (r_2: Z) , forall (i: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH9 : (0 <= islower)) (PreH10 : (islower <= 1)) (PreH11 : (0 <= isupper)) (PreH12 : (isupper <= 1)) ,
  ((( &( "dict_size" ) )) # Int  |-> dict_size_pre)
  **  ((( &( "keys" ) )) # Ptr  |-> keys_pre)
  **  ((( &( "islower" ) )) # Int  |-> islower)
  **  ((( &( "isupper" ) )) # Int  |-> isupper)
  **  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition check_dict_case_entail_wit_1 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (PreH1 : (dict_size_pre <> 0)) (PreH2 : (0 <= dict_size_pre)) (PreH3 : (dict_size_pre <= 100)) (PreH4 : ((Zlength (rows)) = dict_size_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < dict_size_pre)) -> (((0 < (Zlength ((Znth (k) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (k) (rows) ((@nil Z))))) - 1 )) ((Znth (k) (rows) ((@nil Z)))) (0)) = 0)))) (PreH6 : forall (k_2: Z) , forall (i_2: Z) , (((((0 <= k_2) /\ (k_2 < dict_size_pre)) /\ (0 <= i_2)) /\ (i_2 < ((Zlength ((Znth (k_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i_2) ((Znth (k_2) (rows) ((@nil Z)))) (0)) <> 0))) ,
  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows )
) \/
(
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (PreH1 : (dict_size_pre <> 0)) (PreH2 : (0 <= dict_size_pre)) (PreH3 : (dict_size_pre <= 100)) (PreH4 : ((Zlength (rows)) = dict_size_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < dict_size_pre)) -> (((0 < (Zlength ((Znth (k) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (k) (rows) ((@nil Z))))) - 1 )) ((Znth (k) (rows) ((@nil Z)))) (0)) = 0)))) (PreH6 : forall (k_2: Z) , forall (i_2: Z) , (((((0 <= k_2) /\ (k_2 < dict_size_pre)) /\ (0 <= i_2)) /\ (i_2 < ((Zlength ((Znth (k_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i_2) ((Znth (k_2) (rows) ((@nil Z)))) (0)) <> 0))) ,
  TT && emp 
|--
  “ forall (r_2: Z) , forall (i: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ”
  &&  emp
).

Definition check_dict_case_entail_wit_1_split_goal_1 := 
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (PreH1 : (dict_size_pre <> 0)) (PreH2 : (0 <= dict_size_pre)) (PreH3 : (dict_size_pre <= 100)) (PreH4 : ((Zlength (rows)) = dict_size_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < dict_size_pre)) -> (((0 < (Zlength ((Znth (k) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (k) (rows) ((@nil Z))))) - 1 )) ((Znth (k) (rows) ((@nil Z)))) (0)) = 0)))) (PreH6 : forall (k_2: Z) , forall (i_2: Z) , (((((0 <= k_2) /\ (k_2 < dict_size_pre)) /\ (0 <= i_2)) /\ (i_2 < ((Zlength ((Znth (k_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i_2) ((Znth (k_2) (rows) ((@nil Z)))) (0)) <> 0))) ,
  forall (r_2: Z) , forall (i: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))
.

Definition check_dict_case_entail_wit_2 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (k: Z) (PreH1 : (k < dict_size_pre)) (PreH2 : (0 <= k)) (PreH3 : (k <= dict_size_pre)) (PreH4 : (0 <= dict_size_pre)) (PreH5 : (dict_size_pre <= 100)) (PreH6 : ((Zlength (rows)) = dict_size_pre)) (PreH7 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < dict_size_pre)) -> (((0 < (Zlength ((Znth (r_3) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r_3) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r_3) (rows) ((@nil Z))))) - 1 )) ((Znth (r_3) (rows) ((@nil Z)))) (0)) = 0)))) (PreH8 : forall (r_4: Z) , forall (i_2: Z) , (((((0 <= r_4) /\ (r_4 < dict_size_pre)) /\ (0 <= i_2)) /\ (i_2 < ((Zlength ((Znth (r_4) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i_2) ((Znth (r_4) (rows) ((@nil Z)))) (0)) <> 0))) (PreH9 : (0 <= islower)) (PreH10 : (islower <= 1)) (PreH11 : (0 <= isupper)) (PreH12 : (isupper <= 1)) ,
  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 <= islower) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (isupper <= 1) ”
  &&  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
) \/
(
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (k: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth k rows __default__List_Z))))) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 <= k)) (PreH4 : (k <= dict_size_pre)) (PreH5 : (0 <= dict_size_pre)) (PreH6 : (dict_size_pre <= 100)) (PreH7 : ((Zlength (rows)) = dict_size_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < dict_size_pre)) -> (((0 < (Zlength ((Znth (r_3) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r_3) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r_3) (rows) ((@nil Z))))) - 1 )) ((Znth (r_3) (rows) ((@nil Z)))) (0)) = 0)))) (PreH9 : forall (r_4: Z) , forall (i_2: Z) , (((((0 <= r_4) /\ (r_4 < dict_size_pre)) /\ (0 <= i_2)) /\ (i_2 < ((Zlength ((Znth (r_4) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i_2) ((Znth (r_4) (rows) ((@nil Z)))) (0)) <> 0))) (PreH10 : (0 <= islower)) (PreH11 : (islower <= 1)) (PreH12 : (0 <= isupper)) (PreH13 : (isupper <= 1)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth k rows __default__List_Z))) (Znth k rows __default__List_Z) )
|--
  “ forall (r_2: Z) , forall (i: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ”
  &&  (CharArray.full row_ptr_2 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
).

Definition check_dict_case_entail_wit_2_split_goal_1 := 
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (k: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth k rows __default__List_Z))))) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 <= k)) (PreH4 : (k <= dict_size_pre)) (PreH5 : (0 <= dict_size_pre)) (PreH6 : (dict_size_pre <= 100)) (PreH7 : ((Zlength (rows)) = dict_size_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < dict_size_pre)) -> (((0 < (Zlength ((Znth (r_3) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r_3) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r_3) (rows) ((@nil Z))))) - 1 )) ((Znth (r_3) (rows) ((@nil Z)))) (0)) = 0)))) (PreH9 : forall (r_4: Z) , forall (i_2: Z) , (((((0 <= r_4) /\ (r_4 < dict_size_pre)) /\ (0 <= i_2)) /\ (i_2 < ((Zlength ((Znth (r_4) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i_2) ((Znth (r_4) (rows) ((@nil Z)))) (0)) <> 0))) (PreH10 : (0 <= islower)) (PreH11 : (islower <= 1)) (PreH12 : (0 <= isupper)) (PreH13 : (isupper <= 1)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth k rows __default__List_Z))) (Znth k rows __default__List_Z) )
|--
  “ forall (r_2: Z) , forall (i: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ”
.

Definition check_dict_case_entail_wit_2_split_goal_spatial := 
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (k: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth k rows __default__List_Z))))) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 <= k)) (PreH4 : (k <= dict_size_pre)) (PreH5 : (0 <= dict_size_pre)) (PreH6 : (dict_size_pre <= 100)) (PreH7 : ((Zlength (rows)) = dict_size_pre)) (PreH8 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < dict_size_pre)) -> (((0 < (Zlength ((Znth (r_3) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r_3) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r_3) (rows) ((@nil Z))))) - 1 )) ((Znth (r_3) (rows) ((@nil Z)))) (0)) = 0)))) (PreH9 : forall (r_4: Z) , forall (i_2: Z) , (((((0 <= r_4) /\ (r_4 < dict_size_pre)) /\ (0 <= i_2)) /\ (i_2 < ((Zlength ((Znth (r_4) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i_2) ((Znth (r_4) (rows) ((@nil Z)))) (0)) <> 0))) (PreH10 : (0 <= islower)) (PreH11 : (islower <= 1)) (PreH12 : (0 <= isupper)) (PreH13 : (isupper <= 1)) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth k rows __default__List_Z))) (Znth k rows __default__List_Z) )
|--
  (CharArray.full row_ptr_2 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
.

Definition check_dict_case_entail_wit_3 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (k: Z) (islower: Z) (isupper: Z) (PreH1 : (0 <= k)) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 <= dict_size_pre)) (PreH4 : (dict_size_pre <= 100)) (PreH5 : ((Zlength (rows)) = dict_size_pre)) (PreH6 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < dict_size_pre)) -> (((0 < (Zlength ((Znth (r_3) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r_3) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r_3) (rows) ((@nil Z))))) - 1 )) ((Znth (r_3) (rows) ((@nil Z)))) (0)) = 0)))) (PreH7 : forall (r_4: Z) , forall (i_2: Z) , (((((0 <= r_4) /\ (r_4 < dict_size_pre)) /\ (0 <= i_2)) /\ (i_2 < ((Zlength ((Znth (r_4) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i_2) ((Znth (r_4) (rows) ((@nil Z)))) (0)) <> 0))) (PreH8 : (0 <= islower)) (PreH9 : (islower <= 1)) (PreH10 : (0 <= isupper)) (PreH11 : (isupper <= 1)) ,
  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
|--
  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 <= islower) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (isupper <= 1) ”
  &&  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
) \/
(
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (k: Z) (islower: Z) (isupper: Z) (PreH1 : (0 <= k)) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 <= dict_size_pre)) (PreH4 : (dict_size_pre <= 100)) (PreH5 : ((Zlength (rows)) = dict_size_pre)) (PreH6 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < dict_size_pre)) -> (((0 < (Zlength ((Znth (r_3) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r_3) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r_3) (rows) ((@nil Z))))) - 1 )) ((Znth (r_3) (rows) ((@nil Z)))) (0)) = 0)))) (PreH7 : forall (r_4: Z) , forall (i_2: Z) , (((((0 <= r_4) /\ (r_4 < dict_size_pre)) /\ (0 <= i_2)) /\ (i_2 < ((Zlength ((Znth (r_4) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i_2) ((Znth (r_4) (rows) ((@nil Z)))) (0)) <> 0))) (PreH8 : (0 <= islower)) (PreH9 : (islower <= 1)) (PreH10 : (0 <= isupper)) (PreH11 : (isupper <= 1)) ,
  TT && emp 
|--
  “ forall (r_2: Z) , forall (i: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ”
  &&  emp
).

Definition check_dict_case_entail_wit_3_split_goal_1 := 
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (k: Z) (islower: Z) (isupper: Z) (PreH1 : (0 <= k)) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 <= dict_size_pre)) (PreH4 : (dict_size_pre <= 100)) (PreH5 : ((Zlength (rows)) = dict_size_pre)) (PreH6 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < dict_size_pre)) -> (((0 < (Zlength ((Znth (r_3) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r_3) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r_3) (rows) ((@nil Z))))) - 1 )) ((Znth (r_3) (rows) ((@nil Z)))) (0)) = 0)))) (PreH7 : forall (r_4: Z) , forall (i_2: Z) , (((((0 <= r_4) /\ (r_4 < dict_size_pre)) /\ (0 <= i_2)) /\ (i_2 < ((Zlength ((Znth (r_4) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i_2) ((Znth (r_4) (rows) ((@nil Z)))) (0)) <> 0))) (PreH8 : (0 <= islower)) (PreH9 : (islower <= 1)) (PreH10 : (0 <= isupper)) (PreH11 : (isupper <= 1)) ,
  forall (r_2: Z) , forall (i: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))
.

Definition check_dict_case_entail_wit_4 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (k: Z) (islower: Z) (isupper: Z) (PreH1 : (0 <= k)) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 <= dict_size_pre)) (PreH4 : (dict_size_pre <= 100)) (PreH5 : ((Zlength (rows)) = dict_size_pre)) (PreH6 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < dict_size_pre)) -> (((0 < (Zlength ((Znth (r_3) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r_3) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r_3) (rows) ((@nil Z))))) - 1 )) ((Znth (r_3) (rows) ((@nil Z)))) (0)) = 0)))) (PreH7 : forall (r_4: Z) , forall (i: Z) , (((((0 <= r_4) /\ (r_4 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (r_4) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (r_4) (rows) ((@nil Z)))) (0)) <> 0))) (PreH8 : (0 <= islower)) (PreH9 : (islower <= 1)) (PreH10 : (0 <= isupper)) (PreH11 : (isupper <= 1)) ,
  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 <= islower) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (isupper <= 1) ”
  &&  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
) \/
(
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (k: Z) (islower: Z) (isupper: Z) (PreH1 : (0 <= k)) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 <= dict_size_pre)) (PreH4 : (dict_size_pre <= 100)) (PreH5 : ((Zlength (rows)) = dict_size_pre)) (PreH6 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < dict_size_pre)) -> (((0 < (Zlength ((Znth (r_3) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r_3) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r_3) (rows) ((@nil Z))))) - 1 )) ((Znth (r_3) (rows) ((@nil Z)))) (0)) = 0)))) (PreH7 : forall (r_4: Z) , forall (i: Z) , (((((0 <= r_4) /\ (r_4 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (r_4) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (r_4) (rows) ((@nil Z)))) (0)) <> 0))) (PreH8 : (0 <= islower)) (PreH9 : (islower <= 1)) (PreH10 : (0 <= isupper)) (PreH11 : (isupper <= 1)) ,
  TT && emp 
|--
  “ forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ”
  &&  emp
).

Definition check_dict_case_entail_wit_4_split_goal_1 := 
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (k: Z) (islower: Z) (isupper: Z) (PreH1 : (0 <= k)) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 <= dict_size_pre)) (PreH4 : (dict_size_pre <= 100)) (PreH5 : ((Zlength (rows)) = dict_size_pre)) (PreH6 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < dict_size_pre)) -> (((0 < (Zlength ((Znth (r_3) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r_3) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r_3) (rows) ((@nil Z))))) - 1 )) ((Znth (r_3) (rows) ((@nil Z)))) (0)) = 0)))) (PreH7 : forall (r_4: Z) , forall (i: Z) , (((((0 <= r_4) /\ (r_4 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (r_4) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (r_4) (rows) ((@nil Z)))) (0)) <> 0))) (PreH8 : (0 <= islower)) (PreH9 : (islower <= 1)) (PreH10 : (0 <= isupper)) (PreH11 : (isupper <= 1)) ,
  forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))
.

Definition check_dict_case_entail_wit_4_split_goal_2 := 
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (k: Z) (islower: Z) (isupper: Z) (PreH1 : (0 <= k)) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 <= dict_size_pre)) (PreH4 : (dict_size_pre <= 100)) (PreH5 : ((Zlength (rows)) = dict_size_pre)) (PreH6 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < dict_size_pre)) -> (((0 < (Zlength ((Znth (r_3) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r_3) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r_3) (rows) ((@nil Z))))) - 1 )) ((Znth (r_3) (rows) ((@nil Z)))) (0)) = 0)))) (PreH7 : forall (r_4: Z) , forall (i: Z) , (((((0 <= r_4) /\ (r_4 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (r_4) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (r_4) (rows) ((@nil Z)))) (0)) <> 0))) (PreH8 : (0 <= islower)) (PreH9 : (islower <= 1)) (PreH10 : (0 <= isupper)) (PreH11 : (isupper <= 1)) ,
  (0 < (Zlength ((Znth (k) (rows) ((@nil Z))))))
.

Definition check_dict_case_entail_wit_5_1 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((isupper + 1 ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH13 : (0 <= k)) (PreH14 : (k < dict_size_pre)) (PreH15 : (0 <= dict_size_pre)) (PreH16 : (dict_size_pre <= 100)) (PreH17 : ((Zlength (rows)) = dict_size_pre)) (PreH18 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH19 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH20 : (0 <= islower)) (PreH21 : (islower <= 1)) (PreH22 : (0 <= isupper)) (PreH23 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (isupper <= 1) ”
  &&  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
) \/
(
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (k: Z) (i: Z) (PreH1 : ((isupper + 1 ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH13 : (0 <= k)) (PreH14 : (k < dict_size_pre)) (PreH15 : (0 <= dict_size_pre)) (PreH16 : (dict_size_pre <= 100)) (PreH17 : ((Zlength (rows)) = dict_size_pre)) (PreH18 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH19 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH20 : (0 <= islower)) (PreH21 : (islower <= 1)) (PreH22 : (0 <= isupper)) (PreH23 : (isupper <= 1)) ,
  TT && emp 
|--
  “ ((i + 1 ) < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ”
  &&  emp
).

Definition check_dict_case_entail_wit_5_1_split_goal_1 := 
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (k: Z) (i: Z) (PreH1 : ((isupper + 1 ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH13 : (0 <= k)) (PreH14 : (k < dict_size_pre)) (PreH15 : (0 <= dict_size_pre)) (PreH16 : (dict_size_pre <= 100)) (PreH17 : ((Zlength (rows)) = dict_size_pre)) (PreH18 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH19 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH20 : (0 <= islower)) (PreH21 : (islower <= 1)) (PreH22 : (0 <= isupper)) (PreH23 : (isupper <= 1)) ,
  ((i + 1 ) < (Zlength ((Znth (k) (rows) ((@nil Z))))))
.

Definition check_dict_case_entail_wit_5_2 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((1 + islower ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 <= dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : ((Zlength (rows)) = dict_size_pre)) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH17 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH18 : (0 <= islower)) (PreH19 : (islower <= 1)) (PreH20 : (0 <= isupper)) (PreH21 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 <= islower) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ”
  &&  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
) \/
(
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (k: Z) (i: Z) (PreH1 : ((1 + islower ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 <= dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : ((Zlength (rows)) = dict_size_pre)) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH17 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH18 : (0 <= islower)) (PreH19 : (islower <= 1)) (PreH20 : (0 <= isupper)) (PreH21 : (isupper <= 1)) ,
  TT && emp 
|--
  “ ((i + 1 ) < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ”
  &&  emp
).

Definition check_dict_case_entail_wit_5_2_split_goal_1 := 
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (k: Z) (i: Z) (PreH1 : ((1 + islower ) <> 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 <= dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : ((Zlength (rows)) = dict_size_pre)) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH17 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH18 : (0 <= islower)) (PreH19 : (islower <= 1)) (PreH20 : (0 <= isupper)) (PreH21 : (isupper <= 1)) ,
  ((i + 1 ) < (Zlength ((Znth (k) (rows) ((@nil Z))))))
.

Definition check_dict_case_entail_wit_6 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) = 0)) (PreH2 : (0 <= i)) (PreH3 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH4 : (0 <= k)) (PreH5 : (k < dict_size_pre)) (PreH6 : (0 <= dict_size_pre)) (PreH7 : (dict_size_pre <= 100)) (PreH8 : ((Zlength (rows)) = dict_size_pre)) (PreH9 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < dict_size_pre)) -> (((0 < (Zlength ((Znth (r_3) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r_3) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r_3) (rows) ((@nil Z))))) - 1 )) ((Znth (r_3) (rows) ((@nil Z)))) (0)) = 0)))) (PreH10 : forall (r_4: Z) , forall (i0_2: Z) , (((((0 <= r_4) /\ (r_4 < dict_size_pre)) /\ (0 <= i0_2)) /\ (i0_2 < ((Zlength ((Znth (r_4) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0_2) ((Znth (r_4) (rows) ((@nil Z)))) (0)) <> 0))) (PreH11 : (0 <= islower)) (PreH12 : (islower <= 1)) (PreH13 : (0 <= isupper)) (PreH14 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 <= islower) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (isupper <= 1) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows )
) \/
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) = 0)) (PreH3 : (0 <= i)) (PreH4 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH5 : (0 <= k)) (PreH6 : (k < dict_size_pre)) (PreH7 : (0 <= dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : ((Zlength (rows)) = dict_size_pre)) (PreH10 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < dict_size_pre)) -> (((0 < (Zlength ((Znth (r_3) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r_3) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r_3) (rows) ((@nil Z))))) - 1 )) ((Znth (r_3) (rows) ((@nil Z)))) (0)) = 0)))) (PreH11 : forall (r_4: Z) , forall (i0_2: Z) , (((((0 <= r_4) /\ (r_4 < dict_size_pre)) /\ (0 <= i0_2)) /\ (i0_2 < ((Zlength ((Znth (r_4) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0_2) ((Znth (r_4) (rows) ((@nil Z)))) (0)) <> 0))) (PreH12 : (0 <= islower)) (PreH13 : (islower <= 1)) (PreH14 : (0 <= isupper)) (PreH15 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows )
).

Definition check_dict_case_entail_wit_6_split_goal_1 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) = 0)) (PreH3 : (0 <= i)) (PreH4 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH5 : (0 <= k)) (PreH6 : (k < dict_size_pre)) (PreH7 : (0 <= dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : ((Zlength (rows)) = dict_size_pre)) (PreH10 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < dict_size_pre)) -> (((0 < (Zlength ((Znth (r_3) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r_3) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r_3) (rows) ((@nil Z))))) - 1 )) ((Znth (r_3) (rows) ((@nil Z)))) (0)) = 0)))) (PreH11 : forall (r_4: Z) , forall (i0_2: Z) , (((((0 <= r_4) /\ (r_4 < dict_size_pre)) /\ (0 <= i0_2)) /\ (i0_2 < ((Zlength ((Znth (r_4) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0_2) ((Znth (r_4) (rows) ((@nil Z)))) (0)) <> 0))) (PreH12 : (0 <= islower)) (PreH13 : (islower <= 1)) (PreH14 : (0 <= isupper)) (PreH15 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ”
.

Definition check_dict_case_entail_wit_6_split_goal_spatial := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) = 0)) (PreH3 : (0 <= i)) (PreH4 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH5 : (0 <= k)) (PreH6 : (k < dict_size_pre)) (PreH7 : (0 <= dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : ((Zlength (rows)) = dict_size_pre)) (PreH10 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < dict_size_pre)) -> (((0 < (Zlength ((Znth (r_3) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r_3) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r_3) (rows) ((@nil Z))))) - 1 )) ((Znth (r_3) (rows) ((@nil Z)))) (0)) = 0)))) (PreH11 : forall (r_4: Z) , forall (i0_2: Z) , (((((0 <= r_4) /\ (r_4 < dict_size_pre)) /\ (0 <= i0_2)) /\ (i0_2 < ((Zlength ((Znth (r_4) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0_2) ((Znth (r_4) (rows) ((@nil Z)))) (0)) <> 0))) (PreH12 : (0 <= islower)) (PreH13 : (islower <= 1)) (PreH14 : (0 <= isupper)) (PreH15 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full keys_pre dict_size_pre rows )
.

Definition check_dict_case_entail_wit_7 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (k: Z) (islower: Z) (isupper: Z) (PreH1 : (0 <= k)) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 <= islower)) (PreH4 : (islower <= 1)) (PreH5 : (0 <= isupper)) (PreH6 : (isupper <= 1)) (PreH7 : (0 <= dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : ((Zlength (rows)) = dict_size_pre)) (PreH10 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < dict_size_pre)) -> (((0 < (Zlength ((Znth (r_3) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r_3) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r_3) (rows) ((@nil Z))))) - 1 )) ((Znth (r_3) (rows) ((@nil Z)))) (0)) = 0)))) (PreH11 : forall (r_4: Z) , forall (i0: Z) , (((((0 <= r_4) /\ (r_4 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_4) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_4) (rows) ((@nil Z)))) (0)) <> 0))) ,
  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= dict_size_pre) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 <= islower) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (isupper <= 1) ”
  &&  (CharPtrArray2.full keys_pre dict_size_pre rows )
) \/
(
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (k: Z) (islower: Z) (isupper: Z) (PreH1 : (0 <= k)) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 <= islower)) (PreH4 : (islower <= 1)) (PreH5 : (0 <= isupper)) (PreH6 : (isupper <= 1)) (PreH7 : (0 <= dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : ((Zlength (rows)) = dict_size_pre)) (PreH10 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < dict_size_pre)) -> (((0 < (Zlength ((Znth (r_3) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r_3) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r_3) (rows) ((@nil Z))))) - 1 )) ((Znth (r_3) (rows) ((@nil Z)))) (0)) = 0)))) (PreH11 : forall (r_4: Z) , forall (i0: Z) , (((((0 <= r_4) /\ (r_4 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_4) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_4) (rows) ((@nil Z)))) (0)) <> 0))) ,
  TT && emp 
|--
  “ forall (r_2: Z) , forall (i: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ”
  &&  emp
).

Definition check_dict_case_entail_wit_7_split_goal_1 := 
forall (dict_size_pre: Z) (rows: (@list (@list Z))) (k: Z) (islower: Z) (isupper: Z) (PreH1 : (0 <= k)) (PreH2 : (k < dict_size_pre)) (PreH3 : (0 <= islower)) (PreH4 : (islower <= 1)) (PreH5 : (0 <= isupper)) (PreH6 : (isupper <= 1)) (PreH7 : (0 <= dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : ((Zlength (rows)) = dict_size_pre)) (PreH10 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < dict_size_pre)) -> (((0 < (Zlength ((Znth (r_3) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r_3) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r_3) (rows) ((@nil Z))))) - 1 )) ((Znth (r_3) (rows) ((@nil Z)))) (0)) = 0)))) (PreH11 : forall (r_4: Z) , forall (i0: Z) , (((((0 <= r_4) /\ (r_4 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_4) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_4) (rows) ((@nil Z)))) (0)) <> 0))) ,
  forall (r_2: Z) , forall (i: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))
.

Definition check_dict_case_return_wit_1 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (k: Z) (PreH1 : (k >= dict_size_pre)) (PreH2 : (0 <= k)) (PreH3 : (k <= dict_size_pre)) (PreH4 : (0 <= dict_size_pre)) (PreH5 : (dict_size_pre <= 100)) (PreH6 : ((Zlength (rows)) = dict_size_pre)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH8 : forall (r_2: Z) , forall (i: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH9 : (0 <= islower)) (PreH10 : (islower <= 1)) (PreH11 : (0 <= isupper)) (PreH12 : (isupper <= 1)) ,
  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  (CharPtrArray2.full keys_pre dict_size_pre rows )
.

Definition check_dict_case_return_wit_2 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((isupper + 1 ) = 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH11 : (0 <= i)) (PreH12 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH13 : (0 <= k)) (PreH14 : (k < dict_size_pre)) (PreH15 : (0 <= dict_size_pre)) (PreH16 : (dict_size_pre <= 100)) (PreH17 : ((Zlength (rows)) = dict_size_pre)) (PreH18 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH19 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH20 : (0 <= islower)) (PreH21 : (islower <= 1)) (PreH22 : (0 <= isupper)) (PreH23 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full keys_pre dict_size_pre rows )
) \/
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH2 : ((isupper + 1 ) = 2)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH11 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH12 : (0 <= i)) (PreH13 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH14 : (0 <= k)) (PreH15 : (k < dict_size_pre)) (PreH16 : (0 <= dict_size_pre)) (PreH17 : (dict_size_pre <= 100)) (PreH18 : ((Zlength (rows)) = dict_size_pre)) (PreH19 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH20 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH21 : (0 <= islower)) (PreH22 : (islower <= 1)) (PreH23 : (0 <= isupper)) (PreH24 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full keys_pre dict_size_pre rows )
).

Definition check_dict_case_return_wit_2_split_goal_spatial := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH2 : ((isupper + 1 ) = 2)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH10 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH11 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH12 : (0 <= i)) (PreH13 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH14 : (0 <= k)) (PreH15 : (k < dict_size_pre)) (PreH16 : (0 <= dict_size_pre)) (PreH17 : (dict_size_pre <= 100)) (PreH18 : ((Zlength (rows)) = dict_size_pre)) (PreH19 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH20 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH21 : (0 <= islower)) (PreH22 : (islower <= 1)) (PreH23 : (0 <= isupper)) (PreH24 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full keys_pre dict_size_pre rows )
.

Definition check_dict_case_return_wit_3 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((1 + islower ) = 2)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 <= dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : ((Zlength (rows)) = dict_size_pre)) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH17 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH18 : (0 <= islower)) (PreH19 : (islower <= 1)) (PreH20 : (0 <= isupper)) (PreH21 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full keys_pre dict_size_pre rows )
) \/
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH2 : ((1 + islower ) = 2)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH12 : (0 <= k)) (PreH13 : (k < dict_size_pre)) (PreH14 : (0 <= dict_size_pre)) (PreH15 : (dict_size_pre <= 100)) (PreH16 : ((Zlength (rows)) = dict_size_pre)) (PreH17 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH18 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH19 : (0 <= islower)) (PreH20 : (islower <= 1)) (PreH21 : (0 <= isupper)) (PreH22 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full keys_pre dict_size_pre rows )
).

Definition check_dict_case_return_wit_3_split_goal_spatial := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH2 : ((1 + islower ) = 2)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH9 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH12 : (0 <= k)) (PreH13 : (k < dict_size_pre)) (PreH14 : (0 <= dict_size_pre)) (PreH15 : (dict_size_pre <= 100)) (PreH16 : ((Zlength (rows)) = dict_size_pre)) (PreH17 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH18 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH19 : (0 <= islower)) (PreH20 : (islower <= 1)) (PreH21 : (0 <= isupper)) (PreH22 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full keys_pre dict_size_pre rows )
.

Definition check_dict_case_return_wit_4 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH7 : (0 <= k)) (PreH8 : (k < dict_size_pre)) (PreH9 : (0 <= dict_size_pre)) (PreH10 : (dict_size_pre <= 100)) (PreH11 : ((Zlength (rows)) = dict_size_pre)) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH13 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH14 : (0 <= islower)) (PreH15 : (islower <= 1)) (PreH16 : (0 <= isupper)) (PreH17 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full keys_pre dict_size_pre rows )
) \/
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH8 : (0 <= k)) (PreH9 : (k < dict_size_pre)) (PreH10 : (0 <= dict_size_pre)) (PreH11 : (dict_size_pre <= 100)) (PreH12 : ((Zlength (rows)) = dict_size_pre)) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH14 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH15 : (0 <= islower)) (PreH16 : (islower <= 1)) (PreH17 : (0 <= isupper)) (PreH18 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full keys_pre dict_size_pre rows )
).

Definition check_dict_case_return_wit_4_split_goal_spatial := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH8 : (0 <= k)) (PreH9 : (k < dict_size_pre)) (PreH10 : (0 <= dict_size_pre)) (PreH11 : (dict_size_pre <= 100)) (PreH12 : ((Zlength (rows)) = dict_size_pre)) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH14 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH15 : (0 <= islower)) (PreH16 : (islower <= 1)) (PreH17 : (0 <= isupper)) (PreH18 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full keys_pre dict_size_pre rows )
.

Definition check_dict_case_return_wit_5 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 65)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH3 : (0 <= i)) (PreH4 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH5 : (0 <= k)) (PreH6 : (k < dict_size_pre)) (PreH7 : (0 <= dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : ((Zlength (rows)) = dict_size_pre)) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH11 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH12 : (0 <= islower)) (PreH13 : (islower <= 1)) (PreH14 : (0 <= isupper)) (PreH15 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full keys_pre dict_size_pre rows )
) \/
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH4 : (0 <= i)) (PreH5 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH6 : (0 <= k)) (PreH7 : (k < dict_size_pre)) (PreH8 : (0 <= dict_size_pre)) (PreH9 : (dict_size_pre <= 100)) (PreH10 : ((Zlength (rows)) = dict_size_pre)) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH12 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH13 : (0 <= islower)) (PreH14 : (islower <= 1)) (PreH15 : (0 <= isupper)) (PreH16 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full keys_pre dict_size_pre rows )
).

Definition check_dict_case_return_wit_5_split_goal_spatial := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) < 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH4 : (0 <= i)) (PreH5 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH6 : (0 <= k)) (PreH7 : (k < dict_size_pre)) (PreH8 : (0 <= dict_size_pre)) (PreH9 : (dict_size_pre <= 100)) (PreH10 : ((Zlength (rows)) = dict_size_pre)) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH12 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH13 : (0 <= islower)) (PreH14 : (islower <= 1)) (PreH15 : (0 <= isupper)) (PreH16 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full keys_pre dict_size_pre rows )
.

Definition check_dict_case_return_wit_6 := 
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH8 : (0 <= k)) (PreH9 : (k < dict_size_pre)) (PreH10 : (0 <= dict_size_pre)) (PreH11 : (dict_size_pre <= 100)) (PreH12 : ((Zlength (rows)) = dict_size_pre)) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH14 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH15 : (0 <= islower)) (PreH16 : (islower <= 1)) (PreH17 : (0 <= isupper)) (PreH18 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full keys_pre dict_size_pre rows )
) \/
(
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH9 : (0 <= k)) (PreH10 : (k < dict_size_pre)) (PreH11 : (0 <= dict_size_pre)) (PreH12 : (dict_size_pre <= 100)) (PreH13 : ((Zlength (rows)) = dict_size_pre)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH15 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH16 : (0 <= islower)) (PreH17 : (islower <= 1)) (PreH18 : (0 <= isupper)) (PreH19 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full keys_pre dict_size_pre rows )
).

Definition check_dict_case_return_wit_6_split_goal_spatial := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH9 : (0 <= k)) (PreH10 : (k < dict_size_pre)) (PreH11 : (0 <= dict_size_pre)) (PreH12 : (dict_size_pre <= 100)) (PreH13 : ((Zlength (rows)) = dict_size_pre)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH15 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH16 : (0 <= islower)) (PreH17 : (islower <= 1)) (PreH18 : (0 <= isupper)) (PreH19 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full keys_pre dict_size_pre rows )
.

Definition check_dict_case_return_wit_7 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (PreH1 : (dict_size_pre = 0)) (PreH2 : (0 <= dict_size_pre)) (PreH3 : (dict_size_pre <= 100)) (PreH4 : ((Zlength (rows)) = dict_size_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < dict_size_pre)) -> (((0 < (Zlength ((Znth (k) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (k) (rows) ((@nil Z))))) - 1 )) ((Znth (k) (rows) ((@nil Z)))) (0)) = 0)))) (PreH6 : forall (k_2: Z) , forall (i: Z) , (((((0 <= k_2) /\ (k_2 < dict_size_pre)) /\ (0 <= i)) /\ (i < ((Zlength ((Znth (k_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i) ((Znth (k_2) (rows) ((@nil Z)))) (0)) <> 0))) ,
  (CharPtrArray2.full keys_pre dict_size_pre rows )
|--
  (CharPtrArray2.full keys_pre dict_size_pre rows )
.

Definition check_dict_case_partial_solve_wit_1 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH3 : (0 <= k)) (PreH4 : (k < dict_size_pre)) (PreH5 : (0 <= dict_size_pre)) (PreH6 : (dict_size_pre <= 100)) (PreH7 : ((Zlength (rows)) = dict_size_pre)) (PreH8 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH9 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH10 : (0 <= islower)) (PreH11 : (islower <= 1)) (PreH12 : (0 <= isupper)) (PreH13 : (isupper <= 1)) ,
  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
|--
  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 <= islower) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (isupper <= 1) ”
  &&  (((row_ptr + (i * sizeof(CHAR)))) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_2 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH2 : (0 <= i)) (PreH3 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH4 : (0 <= k)) (PreH5 : (k < dict_size_pre)) (PreH6 : (0 <= dict_size_pre)) (PreH7 : (dict_size_pre <= 100)) (PreH8 : ((Zlength (rows)) = dict_size_pre)) (PreH9 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH10 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH11 : (0 <= islower)) (PreH12 : (islower <= 1)) (PreH13 : (0 <= isupper)) (PreH14 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 <= islower) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (isupper <= 1) ”
  &&  (((row_ptr + (i * sizeof(CHAR)))) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_3 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH3 : (0 <= i)) (PreH4 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH5 : (0 <= k)) (PreH6 : (k < dict_size_pre)) (PreH7 : (0 <= dict_size_pre)) (PreH8 : (dict_size_pre <= 100)) (PreH9 : ((Zlength (rows)) = dict_size_pre)) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH11 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH12 : (0 <= islower)) (PreH13 : (islower <= 1)) (PreH14 : (0 <= isupper)) (PreH15 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 <= islower) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (isupper <= 1) ”
  &&  (((row_ptr + (i * sizeof(CHAR)))) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_4 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH4 : (0 <= i)) (PreH5 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH6 : (0 <= k)) (PreH7 : (k < dict_size_pre)) (PreH8 : (0 <= dict_size_pre)) (PreH9 : (dict_size_pre <= 100)) (PreH10 : ((Zlength (rows)) = dict_size_pre)) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH12 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH13 : (0 <= islower)) (PreH14 : (islower <= 1)) (PreH15 : (0 <= isupper)) (PreH16 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 <= islower) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (isupper <= 1) ”
  &&  (((row_ptr + (i * sizeof(CHAR)))) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_5 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH4 : (0 <= i)) (PreH5 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH6 : (0 <= k)) (PreH7 : (k < dict_size_pre)) (PreH8 : (0 <= dict_size_pre)) (PreH9 : (dict_size_pre <= 100)) (PreH10 : ((Zlength (rows)) = dict_size_pre)) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH12 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH13 : (0 <= islower)) (PreH14 : (islower <= 1)) (PreH15 : (0 <= isupper)) (PreH16 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 <= islower) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (isupper <= 1) ”
  &&  (((row_ptr + (i * sizeof(CHAR)))) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_6 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH7 : (0 <= k)) (PreH8 : (k < dict_size_pre)) (PreH9 : (0 <= dict_size_pre)) (PreH10 : (dict_size_pre <= 100)) (PreH11 : ((Zlength (rows)) = dict_size_pre)) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH13 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH14 : (0 <= islower)) (PreH15 : (islower <= 1)) (PreH16 : (0 <= isupper)) (PreH17 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 <= islower) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (isupper <= 1) ”
  &&  (((row_ptr + (i * sizeof(CHAR)))) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_7 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH8 : (0 <= k)) (PreH9 : (k < dict_size_pre)) (PreH10 : (0 <= dict_size_pre)) (PreH11 : (dict_size_pre <= 100)) (PreH12 : ((Zlength (rows)) = dict_size_pre)) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH14 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH15 : (0 <= islower)) (PreH16 : (islower <= 1)) (PreH17 : (0 <= isupper)) (PreH18 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 <= islower) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (isupper <= 1) ”
  &&  (((row_ptr + (i * sizeof(CHAR)))) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_8 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH7 : (0 <= k)) (PreH8 : (k < dict_size_pre)) (PreH9 : (0 <= dict_size_pre)) (PreH10 : (dict_size_pre <= 100)) (PreH11 : ((Zlength (rows)) = dict_size_pre)) (PreH12 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH13 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH14 : (0 <= islower)) (PreH15 : (islower <= 1)) (PreH16 : (0 <= isupper)) (PreH17 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 <= islower) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (isupper <= 1) ”
  &&  (((row_ptr + (i * sizeof(CHAR)))) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_9 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH8 : (0 <= k)) (PreH9 : (k < dict_size_pre)) (PreH10 : (0 <= dict_size_pre)) (PreH11 : (dict_size_pre <= 100)) (PreH12 : ((Zlength (rows)) = dict_size_pre)) (PreH13 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH14 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH15 : (0 <= islower)) (PreH16 : (islower <= 1)) (PreH17 : (0 <= isupper)) (PreH18 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 <= islower) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (isupper <= 1) ”
  &&  (((row_ptr + (i * sizeof(CHAR)))) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_10 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH9 : (0 <= k)) (PreH10 : (k < dict_size_pre)) (PreH11 : (0 <= dict_size_pre)) (PreH12 : (dict_size_pre <= 100)) (PreH13 : ((Zlength (rows)) = dict_size_pre)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH15 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH16 : (0 <= islower)) (PreH17 : (islower <= 1)) (PreH18 : (0 <= isupper)) (PreH19 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 <= islower) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (isupper <= 1) ”
  &&  (((row_ptr + (i * sizeof(CHAR)))) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_11 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH9 : (0 <= k)) (PreH10 : (k < dict_size_pre)) (PreH11 : (0 <= dict_size_pre)) (PreH12 : (dict_size_pre <= 100)) (PreH13 : ((Zlength (rows)) = dict_size_pre)) (PreH14 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH15 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH16 : (0 <= islower)) (PreH17 : (islower <= 1)) (PreH18 : (0 <= isupper)) (PreH19 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 <= islower) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (isupper <= 1) ”
  &&  (((row_ptr + (i * sizeof(CHAR)))) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_12 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH8 : (0 <= i)) (PreH9 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH10 : (0 <= k)) (PreH11 : (k < dict_size_pre)) (PreH12 : (0 <= dict_size_pre)) (PreH13 : (dict_size_pre <= 100)) (PreH14 : ((Zlength (rows)) = dict_size_pre)) (PreH15 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH16 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH17 : (0 <= islower)) (PreH18 : (islower <= 1)) (PreH19 : (0 <= isupper)) (PreH20 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 <= islower) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (isupper <= 1) ”
  &&  (((row_ptr + (i * sizeof(CHAR)))) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
.

Definition check_dict_case_partial_solve_wit_13 := 
forall (dict_size_pre: Z) (keys_pre: Z) (rows: (@list (@list Z))) (isupper: Z) (islower: Z) (row_ptr: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH2 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH3 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH4 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122)) (PreH5 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97)) (PreH6 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90)) (PreH7 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65)) (PreH8 : ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength ((Znth (k) (rows) ((@nil Z))))))) (PreH11 : (0 <= k)) (PreH12 : (k < dict_size_pre)) (PreH13 : (0 <= dict_size_pre)) (PreH14 : (dict_size_pre <= 100)) (PreH15 : ((Zlength (rows)) = dict_size_pre)) (PreH16 : forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0)))) (PreH17 : forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0))) (PreH18 : (0 <= islower)) (PreH19 : (islower <= 1)) (PreH20 : (0 <= isupper)) (PreH21 : (isupper <= 1)) ,
  (CharArray.full row_ptr (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
|--
  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <= 122) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 97) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) > 90) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) >= 65) ” 
  &&  “ ((Znth i (Znth (k) (rows) ((@nil Z))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (Zlength ((Znth (k) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < dict_size_pre) ” 
  &&  “ (0 <= dict_size_pre) ” 
  &&  “ (dict_size_pre <= 100) ” 
  &&  “ ((Zlength (rows)) = dict_size_pre) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < dict_size_pre)) -> (((0 < (Zlength ((Znth (r) (rows) ((@nil Z)))))) /\ ((Zlength ((Znth (r) (rows) ((@nil Z))))) <= 100)) /\ ((Znth (((Zlength ((Znth (r) (rows) ((@nil Z))))) - 1 )) ((Znth (r) (rows) ((@nil Z)))) (0)) = 0))) ” 
  &&  “ forall (r_2: Z) , forall (i0: Z) , (((((0 <= r_2) /\ (r_2 < dict_size_pre)) /\ (0 <= i0)) /\ (i0 < ((Zlength ((Znth (r_2) (rows) ((@nil Z))))) - 1 ))) -> ((Znth (i0) ((Znth (r_2) (rows) ((@nil Z)))) (0)) <> 0)) ” 
  &&  “ (0 <= islower) ” 
  &&  “ (islower <= 1) ” 
  &&  “ (0 <= isupper) ” 
  &&  “ (isupper <= 1) ”
  &&  (((row_ptr + (i * sizeof(CHAR)))) # Char  |-> (Znth i (Znth (k) (rows) ((@nil Z))) 0))
  **  (CharArray.missing_i row_ptr i 0 (Zlength ((Znth (k) (rows) ((@nil Z))))) (Znth (k) (rows) ((@nil Z))) )
  **  (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows )
  **  (((keys_pre + (k * sizeof(PTR)))) # Ptr  |-> row_ptr)
.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.

Axiom proof_of_check_dict_case_safety_wit_1 : check_dict_case_safety_wit_1.
Axiom proof_of_check_dict_case_safety_wit_2 : check_dict_case_safety_wit_2.
Axiom proof_of_check_dict_case_safety_wit_3 : check_dict_case_safety_wit_3.
Axiom proof_of_check_dict_case_safety_wit_4 : check_dict_case_safety_wit_4.
Axiom proof_of_check_dict_case_safety_wit_5 : check_dict_case_safety_wit_5.
Axiom proof_of_check_dict_case_safety_wit_6 : check_dict_case_safety_wit_6.
Axiom proof_of_check_dict_case_safety_wit_7 : check_dict_case_safety_wit_7.
Axiom proof_of_check_dict_case_safety_wit_8 : check_dict_case_safety_wit_8.
Axiom proof_of_check_dict_case_safety_wit_9 : check_dict_case_safety_wit_9.
Axiom proof_of_check_dict_case_safety_wit_10 : check_dict_case_safety_wit_10.
Axiom proof_of_check_dict_case_safety_wit_11 : check_dict_case_safety_wit_11.
Axiom proof_of_check_dict_case_safety_wit_12 : check_dict_case_safety_wit_12.
Axiom proof_of_check_dict_case_safety_wit_13 : check_dict_case_safety_wit_13.
Axiom proof_of_check_dict_case_safety_wit_14 : check_dict_case_safety_wit_14.
Axiom proof_of_check_dict_case_safety_wit_15 : check_dict_case_safety_wit_15.
Axiom proof_of_check_dict_case_safety_wit_16 : check_dict_case_safety_wit_16.
Axiom proof_of_check_dict_case_safety_wit_17 : check_dict_case_safety_wit_17.
Axiom proof_of_check_dict_case_safety_wit_18 : check_dict_case_safety_wit_18.
Axiom proof_of_check_dict_case_safety_wit_19 : check_dict_case_safety_wit_19.
Axiom proof_of_check_dict_case_safety_wit_20 : check_dict_case_safety_wit_20.
Axiom proof_of_check_dict_case_safety_wit_21 : check_dict_case_safety_wit_21.
Axiom proof_of_check_dict_case_safety_wit_22 : check_dict_case_safety_wit_22.
Axiom proof_of_check_dict_case_safety_wit_23 : check_dict_case_safety_wit_23.
Axiom proof_of_check_dict_case_safety_wit_24 : check_dict_case_safety_wit_24.
Axiom proof_of_check_dict_case_safety_wit_25 : check_dict_case_safety_wit_25.
Axiom proof_of_check_dict_case_safety_wit_26 : check_dict_case_safety_wit_26.
Axiom proof_of_check_dict_case_safety_wit_27 : check_dict_case_safety_wit_27.
Axiom proof_of_check_dict_case_safety_wit_28 : check_dict_case_safety_wit_28.
Axiom proof_of_check_dict_case_safety_wit_29 : check_dict_case_safety_wit_29.
Axiom proof_of_check_dict_case_safety_wit_30 : check_dict_case_safety_wit_30.
Axiom proof_of_check_dict_case_safety_wit_31 : check_dict_case_safety_wit_31.
Axiom proof_of_check_dict_case_safety_wit_32 : check_dict_case_safety_wit_32.
Axiom proof_of_check_dict_case_safety_wit_33 : check_dict_case_safety_wit_33.
Axiom proof_of_check_dict_case_safety_wit_34 : check_dict_case_safety_wit_34.
Axiom proof_of_check_dict_case_safety_wit_35 : check_dict_case_safety_wit_35.
Axiom proof_of_check_dict_case_safety_wit_36 : check_dict_case_safety_wit_36.
Axiom proof_of_check_dict_case_safety_wit_37 : check_dict_case_safety_wit_37.
Axiom proof_of_check_dict_case_safety_wit_38 : check_dict_case_safety_wit_38.
Axiom proof_of_check_dict_case_safety_wit_39 : check_dict_case_safety_wit_39.
Axiom proof_of_check_dict_case_safety_wit_40 : check_dict_case_safety_wit_40.
Axiom proof_of_check_dict_case_safety_wit_41 : check_dict_case_safety_wit_41.
Axiom proof_of_check_dict_case_safety_wit_42 : check_dict_case_safety_wit_42.
Axiom proof_of_check_dict_case_entail_wit_1 : check_dict_case_entail_wit_1.
Axiom proof_of_check_dict_case_entail_wit_2 : check_dict_case_entail_wit_2.
Axiom proof_of_check_dict_case_entail_wit_3 : check_dict_case_entail_wit_3.
Axiom proof_of_check_dict_case_entail_wit_4 : check_dict_case_entail_wit_4.
Axiom proof_of_check_dict_case_entail_wit_5_1 : check_dict_case_entail_wit_5_1.
Axiom proof_of_check_dict_case_entail_wit_5_2 : check_dict_case_entail_wit_5_2.
Axiom proof_of_check_dict_case_entail_wit_6 : check_dict_case_entail_wit_6.
Axiom proof_of_check_dict_case_entail_wit_7 : check_dict_case_entail_wit_7.
Axiom proof_of_check_dict_case_return_wit_1 : check_dict_case_return_wit_1.
Axiom proof_of_check_dict_case_return_wit_2 : check_dict_case_return_wit_2.
Axiom proof_of_check_dict_case_return_wit_3 : check_dict_case_return_wit_3.
Axiom proof_of_check_dict_case_return_wit_4 : check_dict_case_return_wit_4.
Axiom proof_of_check_dict_case_return_wit_5 : check_dict_case_return_wit_5.
Axiom proof_of_check_dict_case_return_wit_6 : check_dict_case_return_wit_6.
Axiom proof_of_check_dict_case_return_wit_7 : check_dict_case_return_wit_7.
Axiom proof_of_check_dict_case_partial_solve_wit_1 : check_dict_case_partial_solve_wit_1.
Axiom proof_of_check_dict_case_partial_solve_wit_2 : check_dict_case_partial_solve_wit_2.
Axiom proof_of_check_dict_case_partial_solve_wit_3 : check_dict_case_partial_solve_wit_3.
Axiom proof_of_check_dict_case_partial_solve_wit_4 : check_dict_case_partial_solve_wit_4.
Axiom proof_of_check_dict_case_partial_solve_wit_5 : check_dict_case_partial_solve_wit_5.
Axiom proof_of_check_dict_case_partial_solve_wit_6 : check_dict_case_partial_solve_wit_6.
Axiom proof_of_check_dict_case_partial_solve_wit_7 : check_dict_case_partial_solve_wit_7.
Axiom proof_of_check_dict_case_partial_solve_wit_8 : check_dict_case_partial_solve_wit_8.
Axiom proof_of_check_dict_case_partial_solve_wit_9 : check_dict_case_partial_solve_wit_9.
Axiom proof_of_check_dict_case_partial_solve_wit_10 : check_dict_case_partial_solve_wit_10.
Axiom proof_of_check_dict_case_partial_solve_wit_11 : check_dict_case_partial_solve_wit_11.
Axiom proof_of_check_dict_case_partial_solve_wit_12 : check_dict_case_partial_solve_wit_12.
Axiom proof_of_check_dict_case_partial_solve_wit_13 : check_dict_case_partial_solve_wit_13.

End VC_Correct.
