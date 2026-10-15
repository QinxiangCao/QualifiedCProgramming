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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P025_1384A_common_prefixes_lib.
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
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50)))) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.undef_full out_pre (n_pre + 1 ) 201 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (j: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (n_pre = (Zlength (prefix_lengths)))) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50)))) (PreH5 : (0 <= j)) (PreH6 : (j <= 200)) (PreH7 : (InitialRowProgress n_pre j rows )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (200 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 200) ”
.

Definition solver_safety_wit_3 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (j: Z)  __default__List__App_option_Z (PreH1 : (j < 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50)))) (PreH6 : (0 <= j)) (PreH7 : (j <= 200)) (PreH8 : (InitialRowProgress n_pre j rows )) ,
  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 (Array2.replace_mixed_row (0) ((replace_Znth (j) ((Some (97))) ((Znth 0 rows __default__List__App_option_Z)))) (rows)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full a_pre n_pre prefix_lengths )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_4 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (j: Z) (PreH1 : (j < 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50)))) (PreH6 : (0 <= j)) (PreH7 : (j <= 200)) (PreH8 : (InitialRowProgress n_pre j rows )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (j: Z) (PreH1 : (j < 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50)))) (PreH6 : (0 <= j)) (PreH7 : (j <= 200)) (PreH8 : (InitialRowProgress n_pre j rows )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solver_safety_wit_6 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (j: Z) (PreH1 : (j >= 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50)))) (PreH6 : (0 <= j)) (PreH7 : (j <= 200)) (PreH8 : (InitialRowProgress n_pre j rows )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (j: Z) (PreH1 : (j >= 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50)))) (PreH6 : (0 <= j)) (PreH7 : (j <= 200)) (PreH8 : (InitialRowProgress n_pre j rows )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (200 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 200) ”
.

Definition solver_safety_wit_8 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (j: Z) (PreH1 : (j >= 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50)))) (PreH6 : (0 <= j)) (PreH7 : (j <= 200)) (PreH8 : (InitialRowProgress n_pre j rows )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (j: Z)  __default__List__App_option_Z (PreH1 : (j >= 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50)))) (PreH6 : (0 <= j)) (PreH7 : (j <= 200)) (PreH8 : (InitialRowProgress n_pre j rows )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 (Array2.replace_mixed_row (0) ((replace_Znth (200) ((Some (0))) ((Znth 0 rows __default__List__App_option_Z)))) (rows)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full a_pre n_pre prefix_lengths )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (ProducedRows prefix_lengths (i + 1 ) rows )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_11 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (n_pre = (Zlength (prefix_lengths)))) (PreH4 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= j)) (PreH8 : (j <= 201)) (PreH9 : (CopyProgress prefix_lengths i j rows )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (200 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 200) ”
.

Definition solver_safety_wit_12 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z)  __default__List__App_option_Z (PreH1 : (j <= 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= 201)) (PreH10 : (CopyProgress prefix_lengths i j rows )) ,
  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 (Array2.replace_mixed_row ((i + 1 )) ((replace_Znth (j) ((Some ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (j))))) ((Znth (i + 1 ) (Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (j))))) ((Znth i rows __default__List__App_option_Z)))) (rows)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (j))))) ((Znth i rows __default__List__App_option_Z)))) (rows)))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full a_pre n_pre prefix_lengths )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_13 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z) (PreH1 : (j <= 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= 201)) (PreH10 : (CopyProgress prefix_lengths i j rows )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_14 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z) (PreH1 : (j <= 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= 201)) (PreH10 : (CopyProgress prefix_lengths i j rows )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_15 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (i: Z) (k: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (n_pre = (Zlength (prefix_lengths)))) (PreH4 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (k = (Znth i prefix_lengths 0))) (PreH8 : (0 <= k)) (PreH9 : (k <= 50)) (PreH10 : (CopyProgress prefix_lengths i 201 rows )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_16 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (i: Z) (k: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (n_pre = (Zlength (prefix_lengths)))) (PreH4 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (k = (Znth i prefix_lengths 0))) (PreH8 : (0 <= k)) (PreH9 : (k <= 50)) (PreH10 : (CopyProgress prefix_lengths i 201 rows )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_17 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (i: Z) (k: Z)  __default__List__App_option_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (n_pre = (Zlength (prefix_lengths)))) (PreH4 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (k = (Znth i prefix_lengths 0))) (PreH8 : (0 <= k)) (PreH9 : (k <= 50)) (PreH10 : (CopyProgress prefix_lengths i 201 rows )) ,
  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 (Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k))))) ((Znth i rows __default__List__App_option_Z)))) (rows)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre prefix_lengths )
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solver_safety_wit_18 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (i: Z) (k: Z)  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k)) = 97)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (k = (Znth i prefix_lengths 0))) (PreH9 : (0 <= k)) (PreH10 : (k <= 50)) (PreH11 : (CopyProgress prefix_lengths i 201 rows )) ,
  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 (Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k))))) ((Znth i rows __default__List__App_option_Z)))) (rows)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre prefix_lengths )
|--
  “ (98 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 98) ”
.

Definition solver_safety_wit_19 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (i: Z) (k: Z)  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k)) <> 97)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (k = (Znth i prefix_lengths 0))) (PreH9 : (0 <= k)) (PreH10 : (k <= 50)) (PreH11 : (CopyProgress prefix_lengths i 201 rows )) ,
  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 (Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k))))) ((Znth i rows __default__List__App_option_Z)))) (rows)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre prefix_lengths )
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solver_safety_wit_20 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (i: Z) (k: Z)  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k)) = 97)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (k = (Znth i prefix_lengths 0))) (PreH9 : (0 <= k)) (PreH10 : (k <= 50)) (PreH11 : (CopyProgress prefix_lengths i 201 rows )) ,
  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 (Array2.replace_mixed_row ((i + 1 )) ((replace_Znth (k) ((Some (98))) ((Znth (i + 1 ) (Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k))))) ((Znth i rows __default__List__App_option_Z)))) (rows)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k))))) ((Znth i rows __default__List__App_option_Z)))) (rows)))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre prefix_lengths )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_21 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (i: Z) (k: Z)  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k)) <> 97)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (k = (Znth i prefix_lengths 0))) (PreH9 : (0 <= k)) (PreH10 : (k <= 50)) (PreH11 : (CopyProgress prefix_lengths i 201 rows )) ,
  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 (Array2.replace_mixed_row ((i + 1 )) ((replace_Znth (k) ((Some (97))) ((Znth (i + 1 ) (Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k))))) ((Znth i rows __default__List__App_option_Z)))) (rows)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k))))) ((Znth i rows __default__List__App_option_Z)))) (rows)))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre prefix_lengths )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 prefix_lengths 0)) /\ ((Znth i_2 prefix_lengths 0) <= 50)))) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) ,
  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.undef_full out_pre (n_pre + 1 ) 201 )
|--
  EX (rows: (@list (@list (@option Z)))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (prefix_lengths))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 200) ” 
  &&  “ (InitialRowProgress n_pre 0 rows ) ”
  &&  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
) \/
(
forall (out_pre: Z) (n_pre: Z) (prefix_lengths: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 prefix_lengths 0)) /\ ((Znth i_2 prefix_lengths 0) <= 50)))) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) ,
  (CharArray2.undef_full out_pre (n_pre + 1 ) 201 )
|--
  EX (rows: (@list (@list (@option Z)))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (prefix_lengths))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 200) ” 
  &&  “ (InitialRowProgress n_pre 0 rows ) ”
  &&  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
).

Definition solver_entail_wit_2 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (j: Z)  __default__List__App_option_Z (PreH1 : (j < 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50)))) (PreH6 : (0 <= j)) (PreH7 : (j <= 200)) (PreH8 : (InitialRowProgress n_pre j rows_2 )) ,
  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 (Array2.replace_mixed_row (0) ((replace_Znth (j) ((Some (97))) ((Znth 0 rows_2 __default__List__App_option_Z)))) (rows_2)) )
  **  (IntArray.full a_pre n_pre prefix_lengths )
|--
  EX (rows: (@list (@list (@option Z)))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (prefix_lengths))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50))) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= 200) ” 
  &&  “ (InitialRowProgress n_pre (j + 1 ) rows ) ”
  &&  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
) \/
(
forall (n_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (j: Z)  __default__List__App_option_Z (PreH1 : (j < 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50)))) (PreH6 : (0 <= j)) (PreH7 : (j <= 200)) (PreH8 : (InitialRowProgress n_pre j rows_2 )) ,
  TT && emp 
|--
  “ (InitialRowProgress n_pre (j + 1 ) (Array2.replace_mixed_row (0) ((replace_Znth (j) ((Some (97))) ((Znth 0 rows_2 __default__List__App_option_Z)))) (rows_2)) ) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (j: Z)  __default__List__App_option_Z (PreH1 : (j < 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50)))) (PreH6 : (0 <= j)) (PreH7 : (j <= 200)) (PreH8 : (InitialRowProgress n_pre j rows_2 )) ,
  (InitialRowProgress n_pre (j + 1 ) (Array2.replace_mixed_row (0) ((replace_Znth (j) ((Some (97))) ((Znth 0 rows_2 __default__List__App_option_Z)))) (rows_2)) )
.

Definition solver_entail_wit_3 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (j: Z)  __default__List__App_option_Z (PreH1 : (j >= 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50)))) (PreH6 : (0 <= j)) (PreH7 : (j <= 200)) (PreH8 : (InitialRowProgress n_pre j rows_2 )) ,
  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 (Array2.replace_mixed_row (0) ((replace_Znth (200) ((Some (0))) ((Znth 0 rows_2 __default__List__App_option_Z)))) (rows_2)) )
  **  (IntArray.full a_pre n_pre prefix_lengths )
|--
  EX (rows: (@list (@list (@option Z)))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (prefix_lengths))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (ProducedRows prefix_lengths (0 + 1 ) rows ) ”
  &&  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
) \/
(
forall (n_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (j: Z)  __default__List__App_option_Z (PreH1 : (j >= 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50)))) (PreH6 : (0 <= j)) (PreH7 : (j <= 200)) (PreH8 : (InitialRowProgress n_pre j rows_2 )) ,
  TT && emp 
|--
  “ (ProducedRows prefix_lengths (0 + 1 ) (Array2.replace_mixed_row (0) ((replace_Znth (200) ((Some (0))) ((Znth 0 rows_2 __default__List__App_option_Z)))) (rows_2)) ) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (j: Z)  __default__List__App_option_Z (PreH1 : (j >= 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50)))) (PreH6 : (0 <= j)) (PreH7 : (j <= 200)) (PreH8 : (InitialRowProgress n_pre j rows_2 )) ,
  (ProducedRows prefix_lengths (0 + 1 ) (Array2.replace_mixed_row (0) ((replace_Znth (200) ((Some (0))) ((Znth 0 rows_2 __default__List__App_option_Z)))) (rows_2)) )
.

Definition solver_entail_wit_4 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> ((0 <= (Znth r_2 prefix_lengths 0)) /\ ((Znth r_2 prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (ProducedRows prefix_lengths (i + 1 ) rows_2 )) ,
  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows_2 )
|--
  EX (rows: (@list (@list (@option Z)))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (prefix_lengths))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 201) ” 
  &&  “ (CopyProgress prefix_lengths i 0 rows ) ”
  &&  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
) \/
(
forall (n_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> ((0 <= (Znth r_2 prefix_lengths 0)) /\ ((Znth r_2 prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (ProducedRows prefix_lengths (i + 1 ) rows_2 )) ,
  TT && emp 
|--
  “ (CopyProgress prefix_lengths i 0 rows_2 ) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> ((0 <= (Znth r_2 prefix_lengths 0)) /\ ((Znth r_2 prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (ProducedRows prefix_lengths (i + 1 ) rows_2 )) ,
  (CopyProgress prefix_lengths i 0 rows_2 )
.

Definition solver_entail_wit_5 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (j: Z) (i: Z)  __default__List__App_option_Z (PreH1 : (j <= 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= 201)) (PreH10 : (CopyProgress prefix_lengths i j rows_2 )) ,
  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 (Array2.replace_mixed_row ((i + 1 )) ((replace_Znth (j) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (j))))) ((Znth (i + 1 ) (Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (j))))) ((Znth i rows_2 __default__List__App_option_Z)))) (rows_2)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (j))))) ((Znth i rows_2 __default__List__App_option_Z)))) (rows_2)))) )
  **  (IntArray.full a_pre n_pre prefix_lengths )
|--
  EX (rows: (@list (@list (@option Z)))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (prefix_lengths))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= 201) ” 
  &&  “ (CopyProgress prefix_lengths i (j + 1 ) rows ) ”
  &&  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
) \/
(
forall (n_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (j: Z) (i: Z)  __default__List__App_option_Z (PreH1 : (j <= 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= 201)) (PreH10 : (CopyProgress prefix_lengths i j rows_2 )) ,
  TT && emp 
|--
  “ (CopyProgress prefix_lengths i (j + 1 ) (Array2.replace_mixed_row ((i + 1 )) ((replace_Znth (j) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (j))))) ((Znth (i + 1 ) (Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (j))))) ((Znth i rows_2 __default__List__App_option_Z)))) (rows_2)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (j))))) ((Znth i rows_2 __default__List__App_option_Z)))) (rows_2)))) ) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (j: Z) (i: Z)  __default__List__App_option_Z (PreH1 : (j <= 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= 201)) (PreH10 : (CopyProgress prefix_lengths i j rows_2 )) ,
  (CopyProgress prefix_lengths i (j + 1 ) (Array2.replace_mixed_row ((i + 1 )) ((replace_Znth (j) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (j))))) ((Znth (i + 1 ) (Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (j))))) ((Znth i rows_2 __default__List__App_option_Z)))) (rows_2)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (j))))) ((Znth i rows_2 __default__List__App_option_Z)))) (rows_2)))) )
.

Definition solver_entail_wit_6 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (j: Z) (i: Z) (PreH1 : (j > 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> ((0 <= (Znth r_2 prefix_lengths 0)) /\ ((Znth r_2 prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= 201)) (PreH10 : (CopyProgress prefix_lengths i j rows_2 )) ,
  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows_2 )
|--
  EX (rows: (@list (@list (@option Z)))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (prefix_lengths))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Znth i prefix_lengths 0) = (Znth i prefix_lengths 0)) ” 
  &&  “ (0 <= (Znth i prefix_lengths 0)) ” 
  &&  “ ((Znth i prefix_lengths 0) <= 50) ” 
  &&  “ (CopyProgress prefix_lengths i 201 rows ) ”
  &&  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
) \/
(
forall (n_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (j: Z) (i: Z) (PreH1 : (j > 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> ((0 <= (Znth r_2 prefix_lengths 0)) /\ ((Znth r_2 prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= 201)) (PreH10 : (CopyProgress prefix_lengths i j rows_2 )) ,
  TT && emp 
|--
  “ (CopyProgress prefix_lengths i 201 rows_2 ) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 := 
forall (n_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (j: Z) (i: Z) (PreH1 : (j > 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> ((0 <= (Znth r_2 prefix_lengths 0)) /\ ((Znth r_2 prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= 201)) (PreH10 : (CopyProgress prefix_lengths i j rows_2 )) ,
  (CopyProgress prefix_lengths i 201 rows_2 )
.

Definition solver_entail_wit_7_1 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (i: Z) (k: Z)  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (k)) = 97)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> ((0 <= (Znth r_2 prefix_lengths 0)) /\ ((Znth r_2 prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (k = (Znth i prefix_lengths 0))) (PreH9 : (0 <= k)) (PreH10 : (k <= 50)) (PreH11 : (CopyProgress prefix_lengths i 201 rows_2 )) ,
  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 (Array2.replace_mixed_row ((i + 1 )) ((replace_Znth (k) ((Some (98))) ((Znth (i + 1 ) (Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (k))))) ((Znth i rows_2 __default__List__App_option_Z)))) (rows_2)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (k))))) ((Znth i rows_2 __default__List__App_option_Z)))) (rows_2)))) )
  **  (IntArray.full a_pre n_pre prefix_lengths )
|--
  EX (rows: (@list (@list (@option Z)))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (prefix_lengths))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (ProducedRows prefix_lengths ((i + 1 ) + 1 ) rows ) ”
  &&  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
) \/
(
forall (n_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (i: Z) (k: Z)  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (k)) = 97)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> ((0 <= (Znth r_2 prefix_lengths 0)) /\ ((Znth r_2 prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (k = (Znth i prefix_lengths 0))) (PreH9 : (0 <= k)) (PreH10 : (k <= 50)) (PreH11 : (CopyProgress prefix_lengths i 201 rows_2 )) ,
  TT && emp 
|--
  “ (ProducedRows prefix_lengths ((i + 1 ) + 1 ) (Array2.replace_mixed_row ((i + 1 )) ((replace_Znth (k) ((Some (98))) ((Znth (i + 1 ) (Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (k))))) ((Znth i rows_2 __default__List__App_option_Z)))) (rows_2)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (k))))) ((Znth i rows_2 __default__List__App_option_Z)))) (rows_2)))) ) ”
  &&  emp
).

Definition solver_entail_wit_7_1_split_goal_1 := 
forall (n_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (i: Z) (k: Z)  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (k)) = 97)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> ((0 <= (Znth r_2 prefix_lengths 0)) /\ ((Znth r_2 prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (k = (Znth i prefix_lengths 0))) (PreH9 : (0 <= k)) (PreH10 : (k <= 50)) (PreH11 : (CopyProgress prefix_lengths i 201 rows_2 )) ,
  (ProducedRows prefix_lengths ((i + 1 ) + 1 ) (Array2.replace_mixed_row ((i + 1 )) ((replace_Znth (k) ((Some (98))) ((Znth (i + 1 ) (Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (k))))) ((Znth i rows_2 __default__List__App_option_Z)))) (rows_2)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (k))))) ((Znth i rows_2 __default__List__App_option_Z)))) (rows_2)))) )
.

Definition solver_entail_wit_7_2 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (i: Z) (k: Z)  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (k)) <> 97)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> ((0 <= (Znth r_2 prefix_lengths 0)) /\ ((Znth r_2 prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (k = (Znth i prefix_lengths 0))) (PreH9 : (0 <= k)) (PreH10 : (k <= 50)) (PreH11 : (CopyProgress prefix_lengths i 201 rows_2 )) ,
  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 (Array2.replace_mixed_row ((i + 1 )) ((replace_Znth (k) ((Some (97))) ((Znth (i + 1 ) (Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (k))))) ((Znth i rows_2 __default__List__App_option_Z)))) (rows_2)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (k))))) ((Znth i rows_2 __default__List__App_option_Z)))) (rows_2)))) )
  **  (IntArray.full a_pre n_pre prefix_lengths )
|--
  EX (rows: (@list (@list (@option Z)))) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (prefix_lengths))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (ProducedRows prefix_lengths ((i + 1 ) + 1 ) rows ) ”
  &&  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
) \/
(
forall (n_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (i: Z) (k: Z)  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (k)) <> 97)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> ((0 <= (Znth r_2 prefix_lengths 0)) /\ ((Znth r_2 prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (k = (Znth i prefix_lengths 0))) (PreH9 : (0 <= k)) (PreH10 : (k <= 50)) (PreH11 : (CopyProgress prefix_lengths i 201 rows_2 )) ,
  TT && emp 
|--
  “ (ProducedRows prefix_lengths ((i + 1 ) + 1 ) (Array2.replace_mixed_row ((i + 1 )) ((replace_Znth (k) ((Some (97))) ((Znth (i + 1 ) (Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (k))))) ((Znth i rows_2 __default__List__App_option_Z)))) (rows_2)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (k))))) ((Znth i rows_2 __default__List__App_option_Z)))) (rows_2)))) ) ”
  &&  emp
).

Definition solver_entail_wit_7_2_split_goal_1 := 
forall (n_pre: Z) (prefix_lengths: (@list Z)) (rows_2: (@list (@list (@option Z)))) (i: Z) (k: Z)  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (k)) <> 97)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> ((0 <= (Znth r_2 prefix_lengths 0)) /\ ((Znth r_2 prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (k = (Znth i prefix_lengths 0))) (PreH9 : (0 <= k)) (PreH10 : (k <= 50)) (PreH11 : (CopyProgress prefix_lengths i 201 rows_2 )) ,
  (ProducedRows prefix_lengths ((i + 1 ) + 1 ) (Array2.replace_mixed_row ((i + 1 )) ((replace_Znth (k) ((Some (97))) ((Znth (i + 1 ) (Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (k))))) ((Znth i rows_2 __default__List__App_option_Z)))) (rows_2)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows_2 __default__List__App_option_Z)) (k))))) ((Znth i rows_2 __default__List__App_option_Z)))) (rows_2)))) )
.

Definition solver_return_wit_1 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (i_3: Z)  __default__List_Z (PreH1 : (i_3 >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i_3)) (PreH7 : (i_3 <= n_pre)) (PreH8 : (ProducedRows prefix_lengths (i_3 + 1 ) rows )) ,
  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  EX (out_rows: (@list (@list Z)))  (out_spec: (@list (@list Z))) ,
  “ (Spec prefix_lengths out_spec ) ” 
  &&  “ ((Zlength (out_spec)) = (n_pre + 1 )) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (n_pre + 1 ))) -> ((Zlength ((Znth i out_spec __default__List_Z))) = 200)) ” 
  &&  “ ((Zlength (out_rows)) = (n_pre + 1 )) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (n_pre + 1 ))) -> ((Znth i_2 out_rows __default__List_Z) = (app ((Znth i_2 out_spec __default__List_Z)) ((cons (0) ((@nil Z))))))) ”
  &&  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.full out_pre (n_pre + 1 ) 201 out_rows )
) \/
(
forall (n_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (i_3: Z)  __default__List_Z (PreH1 : (i_3 >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i_3)) (PreH7 : (i_3 <= n_pre)) (PreH8 : (ProducedRows prefix_lengths (i_3 + 1 ) rows )) ,
  TT && emp 
|--
  EX (out_rows: (@list (@list Z)))  (out_spec: (@list (@list Z))) ,
  “ (rows = (Array2.some_rows (out_rows))) ” 
  &&  “ (Spec prefix_lengths out_spec ) ” 
  &&  “ ((Zlength (out_spec)) = ((Zlength (prefix_lengths)) + 1 )) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < ((Zlength (prefix_lengths)) + 1 ))) -> ((Zlength ((Znth i out_spec __default__List_Z))) = 200)) ” 
  &&  “ ((Zlength (out_rows)) = ((Zlength (prefix_lengths)) + 1 )) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < ((Zlength (prefix_lengths)) + 1 ))) -> ((Znth i_2 out_rows __default__List_Z) = (app ((Znth i_2 out_spec __default__List_Z)) ((cons (0) ((@nil Z))))))) ”
  &&  emp
).

Definition solver_partial_solve_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (j: Z)  __default__List__App_option_Z (PreH1 : (j < 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50)))) (PreH6 : (0 <= j)) (PreH7 : (j <= 200)) (PreH8 : (InitialRowProgress n_pre j rows )) ,
  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (j < 200) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (prefix_lengths))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= 200) ” 
  &&  “ (InitialRowProgress n_pre j rows ) ”
  &&  ((((out_pre + (0 * (sizeof(CHAR) * 201))) + (j * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.mixed_missing_i (out_pre + (0 * (sizeof(CHAR) * 201))) j 0 201 (Znth 0 rows __default__List__App_option_Z) )
  **  (CharArray2.mixed_missing_i out_pre 0 0 (n_pre + 1 ) 201 rows )
  **  (IntArray.full a_pre n_pre prefix_lengths )
.

Definition solver_partial_solve_wit_2 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (j: Z)  __default__List__App_option_Z (PreH1 : (j >= 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50)))) (PreH6 : (0 <= j)) (PreH7 : (j <= 200)) (PreH8 : (InitialRowProgress n_pre j rows )) ,
  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (j >= 200) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (prefix_lengths))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i prefix_lengths 0)) /\ ((Znth i prefix_lengths 0) <= 50))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= 200) ” 
  &&  “ (InitialRowProgress n_pre j rows ) ”
  &&  ((((out_pre + (0 * (sizeof(CHAR) * 201))) + (200 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.mixed_missing_i (out_pre + (0 * (sizeof(CHAR) * 201))) 200 0 201 (Znth 0 rows __default__List__App_option_Z) )
  **  (CharArray2.mixed_missing_i out_pre 0 0 (n_pre + 1 ) 201 rows )
  **  (IntArray.full a_pre n_pre prefix_lengths )
.

Definition solver_partial_solve_wit_3_pure := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z)  __default__List__App_option_Z (PreH1 : (j <= 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= 201)) (PreH10 : (CopyProgress prefix_lengths i j rows )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (Array2.mixed_def (Znth i rows __default__List__App_option_Z) j ) ”
) \/
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z)  __default__List__App_option_Z (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (j >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j <= 200)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (n_pre = (Zlength (prefix_lengths)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= 201)) (PreH16 : (CopyProgress prefix_lengths i j rows )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (Array2.mixed_def (Znth i rows __default__List__App_option_Z) j ) ”
).

Definition solver_partial_solve_wit_3_pure_split_goal_1 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z)  __default__List__App_option_Z (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (j >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j <= 200)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : (n_pre = (Zlength (prefix_lengths)))) (PreH11 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= 201)) (PreH16 : (CopyProgress prefix_lengths i j rows )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (Array2.mixed_def (Znth i rows __default__List__App_option_Z) j ) ”
.

Definition solver_partial_solve_wit_3_aux := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z)  __default__List__App_option_Z (PreH1 : (j <= 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= 201)) (PreH10 : (CopyProgress prefix_lengths i j rows )) ,
  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (Array2.mixed_def (Znth i rows __default__List__App_option_Z) j ) ” 
  &&  “ (j <= 200) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (prefix_lengths))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= 201) ” 
  &&  “ (CopyProgress prefix_lengths i j rows ) ”
  &&  ((((out_pre + (i * (sizeof(CHAR) * 201))) + (j * sizeof(CHAR)))) # Char  |-> (Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (j)))
  **  (CharArray.mixed_missing_i (out_pre + (i * (sizeof(CHAR) * 201))) j 0 201 (Znth i rows __default__List__App_option_Z) )
  **  (CharArray2.mixed_missing_i out_pre i 0 (n_pre + 1 ) 201 rows )
  **  (IntArray.full a_pre n_pre prefix_lengths )
.

Definition solver_partial_solve_wit_3 := solver_partial_solve_wit_3_pure -> solver_partial_solve_wit_3_aux.

Definition solver_partial_solve_wit_4 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z)  __default__List__App_option_Z (PreH1 : (j <= 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= 201)) (PreH10 : (CopyProgress prefix_lengths i j rows )) ,
  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 (Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (j))))) ((Znth i rows __default__List__App_option_Z)))) (rows)) )
  **  (IntArray.full a_pre n_pre prefix_lengths )
|--
  “ (j <= 200) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (prefix_lengths))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= 201) ” 
  &&  “ (CopyProgress prefix_lengths i j rows ) ”
  &&  ((((out_pre + ((i + 1 ) * (sizeof(CHAR) * 201))) + (j * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.mixed_missing_i (out_pre + ((i + 1 ) * (sizeof(CHAR) * 201))) j 0 201 (Znth (i + 1 ) (Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (j))))) ((Znth i rows __default__List__App_option_Z)))) (rows)) __default__List__App_option_Z) )
  **  (CharArray2.mixed_missing_i out_pre (i + 1 ) 0 (n_pre + 1 ) 201 (Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (j))))) ((Znth i rows __default__List__App_option_Z)))) (rows)) )
  **  (IntArray.full a_pre n_pre prefix_lengths )
.

Definition solver_partial_solve_wit_5 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (j: Z) (i: Z) (PreH1 : (j > 200)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= 201)) (PreH10 : (CopyProgress prefix_lengths i j rows )) ,
  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (j > 200) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (prefix_lengths))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= 201) ” 
  &&  “ (CopyProgress prefix_lengths i j rows ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i prefix_lengths 0))
  **  (IntArray.missing_i a_pre i 0 n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
.

Definition solver_partial_solve_wit_6_pure := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (i: Z) (k: Z)  __default__List__App_option_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (n_pre = (Zlength (prefix_lengths)))) (PreH4 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (k = (Znth i prefix_lengths 0))) (PreH8 : (0 <= k)) (PreH9 : (k <= 50)) (PreH10 : (CopyProgress prefix_lengths i 201 rows )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (Array2.mixed_def (Znth i rows __default__List__App_option_Z) k ) ”
) \/
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (i: Z) (k: Z)  __default__List__App_option_Z (PreH1 : (k <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (k >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (n_pre = (Zlength (prefix_lengths)))) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (k = (Znth i prefix_lengths 0))) (PreH14 : (0 <= k)) (PreH15 : (k <= 50)) (PreH16 : (CopyProgress prefix_lengths i 201 rows )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (Array2.mixed_def (Znth i rows __default__List__App_option_Z) k ) ”
).

Definition solver_partial_solve_wit_6_pure_split_goal_1 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (i: Z) (k: Z)  __default__List__App_option_Z (PreH1 : (k <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (k >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : (n_pre = (Zlength (prefix_lengths)))) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (k = (Znth i prefix_lengths 0))) (PreH14 : (0 <= k)) (PreH15 : (k <= 50)) (PreH16 : (CopyProgress prefix_lengths i 201 rows )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (Array2.mixed_def (Znth i rows __default__List__App_option_Z) k ) ”
.

Definition solver_partial_solve_wit_6_aux := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (i: Z) (k: Z)  __default__List__App_option_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (n_pre = (Zlength (prefix_lengths)))) (PreH4 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (k = (Znth i prefix_lengths 0))) (PreH8 : (0 <= k)) (PreH9 : (k <= 50)) (PreH10 : (CopyProgress prefix_lengths i 201 rows )) ,
  (IntArray.full a_pre n_pre prefix_lengths )
  **  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 rows )
|--
  “ (Array2.mixed_def (Znth i rows __default__List__App_option_Z) k ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (prefix_lengths))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (k = (Znth i prefix_lengths 0)) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= 50) ” 
  &&  “ (CopyProgress prefix_lengths i 201 rows ) ”
  &&  ((((out_pre + (i * (sizeof(CHAR) * 201))) + (k * sizeof(CHAR)))) # Char  |-> (Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k)))
  **  (CharArray.mixed_missing_i (out_pre + (i * (sizeof(CHAR) * 201))) k 0 201 (Znth i rows __default__List__App_option_Z) )
  **  (CharArray2.mixed_missing_i out_pre i 0 (n_pre + 1 ) 201 rows )
  **  (IntArray.full a_pre n_pre prefix_lengths )
.

Definition solver_partial_solve_wit_6 := solver_partial_solve_wit_6_pure -> solver_partial_solve_wit_6_aux.

Definition solver_partial_solve_wit_7 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (i: Z) (k: Z)  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k)) = 97)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (k = (Znth i prefix_lengths 0))) (PreH9 : (0 <= k)) (PreH10 : (k <= 50)) (PreH11 : (CopyProgress prefix_lengths i 201 rows )) ,
  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 (Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k))))) ((Znth i rows __default__List__App_option_Z)))) (rows)) )
  **  (IntArray.full a_pre n_pre prefix_lengths )
|--
  “ ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k)) = 97) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (prefix_lengths))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (k = (Znth i prefix_lengths 0)) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= 50) ” 
  &&  “ (CopyProgress prefix_lengths i 201 rows ) ”
  &&  ((((out_pre + ((i + 1 ) * (sizeof(CHAR) * 201))) + (k * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.mixed_missing_i (out_pre + ((i + 1 ) * (sizeof(CHAR) * 201))) k 0 201 (Znth (i + 1 ) (Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k))))) ((Znth i rows __default__List__App_option_Z)))) (rows)) __default__List__App_option_Z) )
  **  (CharArray2.mixed_missing_i out_pre (i + 1 ) 0 (n_pre + 1 ) 201 (Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k))))) ((Znth i rows __default__List__App_option_Z)))) (rows)) )
  **  (IntArray.full a_pre n_pre prefix_lengths )
.

Definition solver_partial_solve_wit_8 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (prefix_lengths: (@list Z)) (rows: (@list (@list (@option Z)))) (i: Z) (k: Z)  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k)) <> 97)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (prefix_lengths)))) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (k = (Znth i prefix_lengths 0))) (PreH9 : (0 <= k)) (PreH10 : (k <= 50)) (PreH11 : (CopyProgress prefix_lengths i 201 rows )) ,
  (CharArray2.mixed_full out_pre (n_pre + 1 ) 201 (Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k))))) ((Znth i rows __default__List__App_option_Z)))) (rows)) )
  **  (IntArray.full a_pre n_pre prefix_lengths )
|--
  “ ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k)) <> 97) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (prefix_lengths))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((0 <= (Znth r prefix_lengths 0)) /\ ((Znth r prefix_lengths 0) <= 50))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (k = (Znth i prefix_lengths 0)) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= 50) ” 
  &&  “ (CopyProgress prefix_lengths i 201 rows ) ”
  &&  ((((out_pre + ((i + 1 ) * (sizeof(CHAR) * 201))) + (k * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.mixed_missing_i (out_pre + ((i + 1 ) * (sizeof(CHAR) * 201))) k 0 201 (Znth (i + 1 ) (Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k))))) ((Znth i rows __default__List__App_option_Z)))) (rows)) __default__List__App_option_Z) )
  **  (CharArray2.mixed_missing_i out_pre (i + 1 ) 0 (n_pre + 1 ) 201 (Array2.replace_mixed_row (i) ((replace_Znth (k) ((Some ((Array2.mixed_val ((Znth i rows __default__List__App_option_Z)) (k))))) ((Znth i rows __default__List__App_option_Z)))) (rows)) )
  **  (IntArray.full a_pre n_pre prefix_lengths )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Axiom proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3_pure : solver_partial_solve_wit_3_pure.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6_pure : solver_partial_solve_wit_6_pure.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.

End VC_Correct.
