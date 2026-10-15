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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P070_886D_restoration_of_string_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (PreH1 : (Pre g )) (PreH2 : (1 <= (Zlength (g)))) (PreH3 : ((Zlength (g)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (g)))) -> ((0 < (Zlength ((Znth (i) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (i) (g) ((@nil Z))))) <= 100000)))) (PreH5 : forall (i_2: Z) , forall (j: Z) , (((((0 <= i_2) /\ (i_2 < (Zlength (g)))) /\ (0 <= j)) /\ (j < (Zlength ((Znth (i_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (j) ((Znth (i_2) (g) ((@nil Z)))) (0))) /\ ((Znth (j) ((Znth (i_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH6 : (n_pre = (Zlength (g)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((((Znth (i_3) (rows) ((@nil Z))) = (c_string ((Znth (i_3) (g) ((@nil Z)))))) /\ (valid_string (Znth (i_3) (g) ((@nil Z))) )) /\ ((string_length ((Znth (i_3) (g) ((@nil Z))))) < INT_MAX)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full ( &( "used" ) ) 26 (repeat_Z (0) (26)) )
  **  (IntArray.undef_full ( &( "prev" ) ) 26 )
  **  (IntArray.undef_full ( &( "next" ) ) 26 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l: (@list Z)) (prev_prefix: (@list Z)) (next_prefix: (@list Z)) (i: Z) (PreH1 : (Pre g )) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH7 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH8 : (0 <= i)) (PreH9 : (i <= 26)) (PreH10 : ((Zlength (next_prefix)) = i)) (PreH11 : ((Zlength (prev_prefix)) = i)) (PreH12 : (InitState next_prefix prev_prefix used_l )) ,
  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.seg ( &( "next" ) ) 0 i next_prefix )
  **  (IntArray.undef_seg ( &( "next" ) ) i 26 )
  **  (IntArray.seg ( &( "prev" ) ) 0 i prev_prefix )
  **  (IntArray.undef_seg ( &( "prev" ) ) i 26 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
|--
  “ (26 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 26) ”
.

Definition solver_safety_wit_3 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l: (@list Z)) (prev_prefix: (@list Z)) (next_prefix: (@list Z)) (i: Z) (PreH1 : (i < 26)) (PreH2 : (Pre g )) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= i)) (PreH10 : (i <= 26)) (PreH11 : ((Zlength (next_prefix)) = i)) (PreH12 : ((Zlength (prev_prefix)) = i)) (PreH13 : (InitState next_prefix prev_prefix used_l )) ,
  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.seg ( &( "next" ) ) 0 i next_prefix )
  **  (IntArray.undef_seg ( &( "next" ) ) i 26 )
  **  (IntArray.seg ( &( "prev" ) ) 0 i prev_prefix )
  **  (IntArray.undef_seg ( &( "prev" ) ) i 26 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_4 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l: (@list Z)) (prev_prefix: (@list Z)) (next_prefix: (@list Z)) (i: Z) (PreH1 : (i < 26)) (PreH2 : (Pre g )) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= i)) (PreH10 : (i <= 26)) (PreH11 : ((Zlength (next_prefix)) = i)) (PreH12 : ((Zlength (prev_prefix)) = i)) (PreH13 : (InitState next_prefix prev_prefix used_l )) ,
  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.seg ( &( "next" ) ) 0 i next_prefix )
  **  (IntArray.undef_seg ( &( "next" ) ) i 26 )
  **  (IntArray.seg ( &( "prev" ) ) 0 i prev_prefix )
  **  (IntArray.undef_seg ( &( "prev" ) ) i 26 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l: (@list Z)) (prev_prefix: (@list Z)) (next_prefix: (@list Z)) (i: Z) (PreH1 : (i < 26)) (PreH2 : (Pre g )) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= i)) (PreH10 : (i <= 26)) (PreH11 : ((Zlength (next_prefix)) = i)) (PreH12 : ((Zlength (prev_prefix)) = i)) (PreH13 : (InitState next_prefix prev_prefix used_l )) ,
  (IntArray.seg ( &( "prev" ) ) 0 (i + 1 ) (app (prev_prefix) ((cons ((-1)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "prev" ) ) (i + 1 ) 26 )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.seg ( &( "next" ) ) 0 i next_prefix )
  **  (IntArray.undef_seg ( &( "next" ) ) i 26 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_6 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l: (@list Z)) (prev_prefix: (@list Z)) (next_prefix: (@list Z)) (i: Z) (PreH1 : (i < 26)) (PreH2 : (Pre g )) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= i)) (PreH10 : (i <= 26)) (PreH11 : ((Zlength (next_prefix)) = i)) (PreH12 : ((Zlength (prev_prefix)) = i)) (PreH13 : (InitState next_prefix prev_prefix used_l )) ,
  (IntArray.seg ( &( "prev" ) ) 0 (i + 1 ) (app (prev_prefix) ((cons ((-1)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "prev" ) ) (i + 1 ) 26 )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.seg ( &( "next" ) ) 0 i next_prefix )
  **  (IntArray.undef_seg ( &( "next" ) ) i 26 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_7 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l: (@list Z)) (prev_prefix: (@list Z)) (next_prefix: (@list Z)) (i: Z) (PreH1 : (i < 26)) (PreH2 : (Pre g )) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= i)) (PreH10 : (i <= 26)) (PreH11 : ((Zlength (next_prefix)) = i)) (PreH12 : ((Zlength (prev_prefix)) = i)) (PreH13 : (InitState next_prefix prev_prefix used_l )) ,
  (IntArray.seg ( &( "next" ) ) 0 (i + 1 ) (app (next_prefix) ((cons ((-1)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "next" ) ) (i + 1 ) 26 )
  **  (IntArray.seg ( &( "prev" ) ) 0 (i + 1 ) (app (prev_prefix) ((cons ((-1)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "prev" ) ) (i + 1 ) 26 )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_8 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l: (@list Z)) (prev_prefix: (@list Z)) (next_prefix: (@list Z)) (i: Z) (PreH1 : (i >= 26)) (PreH2 : (Pre g )) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= i)) (PreH10 : (i <= 26)) (PreH11 : ((Zlength (next_prefix)) = i)) (PreH12 : ((Zlength (prev_prefix)) = i)) (PreH13 : (InitState next_prefix prev_prefix used_l )) ,
  ((( &( "z" ) )) # Int  |->_)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.seg ( &( "next" ) ) 0 i next_prefix )
  **  (IntArray.undef_seg ( &( "next" ) ) i 26 )
  **  (IntArray.seg ( &( "prev" ) ) 0 i prev_prefix )
  **  (IntArray.undef_seg ( &( "prev" ) ) i 26 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l: (@list Z)) (prev_l: (@list Z)) (used_l: (@list Z)) (row_ptr: Z) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : ((Zlength (next_l)) = 26)) (PreH10 : ((Zlength (prev_l)) = 26)) (PreH11 : ((Zlength (used_l)) = 26)) (PreH12 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH14 : (GraphBuildState g z next_l prev_l used_l )) ,
  ((( &( "last" ) )) # Int  |->_)
  **  (IntArray.full ( &( "seen" ) ) 26 (repeat_Z (0) (26)) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  (CharPtrArray2.missing_i words_pre n_pre z row_ptr rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_10 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l: (@list Z)) (prev_l: (@list Z)) (used_l: (@list Z)) (row_ptr: Z) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : ((Zlength (next_l)) = 26)) (PreH10 : ((Zlength (prev_l)) = 26)) (PreH11 : ((Zlength (used_l)) = 26)) (PreH12 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH14 : (GraphBuildState g z next_l prev_l used_l )) ,
  ((( &( "last" ) )) # Int  |->_)
  **  (IntArray.full ( &( "seen" ) ) 26 (repeat_Z (0) (26)) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  (CharPtrArray2.missing_i words_pre n_pre z row_ptr rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_11 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l: (@list Z)) (prev_l: (@list Z)) (used_l: (@list Z)) (row_ptr: Z) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : ((Zlength (next_l)) = 26)) (PreH10 : ((Zlength (prev_l)) = 26)) (PreH11 : ((Zlength (used_l)) = 26)) (PreH12 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH14 : (GraphBuildState g z next_l prev_l used_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "last" ) )) # Int  |-> (-1))
  **  (IntArray.full ( &( "seen" ) ) 26 (repeat_Z (0) (26)) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  (CharPtrArray2.missing_i words_pre n_pre z row_ptr rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_12 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : (0 <= z)) (PreH7 : (z < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH10 : ((-1) <= last)) (PreH11 : (last < 26)) (PreH12 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH13 : ((Zlength (next_l)) = 26)) (PreH14 : ((Zlength (prev_l)) = 26)) (PreH15 : ((Zlength (used_l)) = 26)) (PreH16 : ((Zlength (seen_l)) = 26)) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH19 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH20 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
|--
  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ”
) \/
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : (0 <= z)) (PreH7 : (z < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH10 : ((-1) <= last)) (PreH11 : (last < 26)) (PreH12 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH13 : ((Zlength (next_l)) = 26)) (PreH14 : ((Zlength (prev_l)) = 26)) (PreH15 : ((Zlength (used_l)) = 26)) (PreH16 : ((Zlength (seen_l)) = 26)) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH19 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH20 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
|--
  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ”
).

Definition solver_safety_wit_12_split_goal_1 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : (0 <= z)) (PreH7 : (z < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH10 : ((-1) <= last)) (PreH11 : (last < 26)) (PreH12 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH13 : ((Zlength (next_l)) = 26)) (PreH14 : ((Zlength (prev_l)) = 26)) (PreH15 : ((Zlength (used_l)) = 26)) (PreH16 : ((Zlength (seen_l)) = 26)) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH19 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH20 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
|--
  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) <= INT_MAX) ”
.

Definition solver_safety_wit_12_split_goal_2 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : (0 <= z)) (PreH7 : (z < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH10 : ((-1) <= last)) (PreH11 : (last < 26)) (PreH12 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH13 : ((Zlength (next_l)) = 26)) (PreH14 : ((Zlength (prev_l)) = 26)) (PreH15 : ((Zlength (used_l)) = 26)) (PreH16 : ((Zlength (seen_l)) = 26)) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH19 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH20 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
|--
  “ ((INT_MIN) <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ”
.

Definition solver_safety_wit_13 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : (0 <= z)) (PreH7 : (z < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH10 : ((-1) <= last)) (PreH11 : (last < 26)) (PreH12 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH13 : ((Zlength (next_l)) = 26)) (PreH14 : ((Zlength (prev_l)) = 26)) (PreH15 : ((Zlength (used_l)) = 26)) (PreH16 : ((Zlength (seen_l)) = 26)) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH19 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH20 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solver_safety_wit_14 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH2 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH3 : (last <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (z <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (last >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (z >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH12 : (n_pre = (Zlength (g)))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100000)) (PreH15 : ((Zlength (rows)) = n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH17 : (0 <= z)) (PreH18 : (z < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH21 : ((-1) <= last)) (PreH22 : (last < 26)) (PreH23 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH24 : ((Zlength (next_l)) = 26)) (PreH25 : ((Zlength (prev_l)) = 26)) (PreH26 : ((Zlength (used_l)) = 26)) (PreH27 : ((Zlength (seen_l)) = 26)) (PreH28 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH29 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH30 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH31 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) ,
  ((( &( "c" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_15 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH2 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH3 : (last <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (z <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (last >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (z >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH12 : (n_pre = (Zlength (g)))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100000)) (PreH15 : ((Zlength (rows)) = n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH17 : (0 <= z)) (PreH18 : (z < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH21 : ((-1) <= last)) (PreH22 : (last < 26)) (PreH23 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH24 : ((Zlength (next_l)) = 26)) (PreH25 : ((Zlength (prev_l)) = 26)) (PreH26 : ((Zlength (used_l)) = 26)) (PreH27 : ((Zlength (seen_l)) = 26)) (PreH28 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH29 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH30 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH31 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH32 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) <> 0)) ,
  (IntArray.full ( &( "seen" ) ) 26 seen_l )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  ((( &( "c" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_16 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH2 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH3 : (last <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (z <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (last >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (z >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH12 : (n_pre = (Zlength (g)))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100000)) (PreH15 : ((Zlength (rows)) = n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH17 : (0 <= z)) (PreH18 : (z < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH21 : ((-1) <= last)) (PreH22 : (last < 26)) (PreH23 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH24 : ((Zlength (next_l)) = 26)) (PreH25 : ((Zlength (prev_l)) = 26)) (PreH26 : ((Zlength (used_l)) = 26)) (PreH27 : ((Zlength (seen_l)) = 26)) (PreH28 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH29 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH30 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH31 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH32 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "seen" ) ) 26 seen_l )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  ((( &( "c" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_17 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH2 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH3 : (last <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (z <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (last >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (z >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH12 : (n_pre = (Zlength (g)))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100000)) (PreH15 : ((Zlength (rows)) = n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH17 : (0 <= z)) (PreH18 : (z < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH21 : ((-1) <= last)) (PreH22 : (last < 26)) (PreH23 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH24 : ((Zlength (next_l)) = 26)) (PreH25 : ((Zlength (prev_l)) = 26)) (PreH26 : ((Zlength (used_l)) = 26)) (PreH27 : ((Zlength (seen_l)) = 26)) (PreH28 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH29 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH30 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH31 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH32 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  ((( &( "c" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_18 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (last >= 0)) (PreH2 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH4 : (last <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (z <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (last >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (z >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH13 : (n_pre = (Zlength (g)))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : ((Zlength (rows)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH18 : (0 <= z)) (PreH19 : (z < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH22 : ((-1) <= last)) (PreH23 : (last < 26)) (PreH24 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH25 : ((Zlength (next_l)) = 26)) (PreH26 : ((Zlength (prev_l)) = 26)) (PreH27 : ((Zlength (used_l)) = 26)) (PreH28 : ((Zlength (seen_l)) = 26)) (PreH29 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH30 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH31 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH32 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH33 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  ((( &( "c" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_19 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH2 : ((Znth last next_l 0) >= 0)) (PreH3 : (last >= 0)) (PreH4 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH6 : (last <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (z <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (last >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (z >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH15 : (n_pre = (Zlength (g)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 100000)) (PreH18 : ((Zlength (rows)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH20 : (0 <= z)) (PreH21 : (z < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH24 : ((-1) <= last)) (PreH25 : (last < 26)) (PreH26 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH27 : ((Zlength (next_l)) = 26)) (PreH28 : ((Zlength (prev_l)) = 26)) (PreH29 : ((Zlength (used_l)) = 26)) (PreH30 : ((Zlength (seen_l)) = 26)) (PreH31 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH32 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH33 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH34 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH35 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  ((( &( "c" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_20 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth last next_l 0) < 0)) (PreH2 : (last >= 0)) (PreH3 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH4 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH5 : (last <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (z <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (last >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (z >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH14 : (n_pre = (Zlength (g)))) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 100000)) (PreH17 : ((Zlength (rows)) = n_pre)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH19 : (0 <= z)) (PreH20 : (z < n_pre)) (PreH21 : (0 <= i)) (PreH22 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH23 : ((-1) <= last)) (PreH24 : (last < 26)) (PreH25 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH26 : ((Zlength (next_l)) = 26)) (PreH27 : ((Zlength (prev_l)) = 26)) (PreH28 : ((Zlength (used_l)) = 26)) (PreH29 : ((Zlength (seen_l)) = 26)) (PreH30 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH31 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH32 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH33 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH34 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  ((( &( "c" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_21 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth last next_l 0) <> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH2 : ((Znth last next_l 0) >= 0)) (PreH3 : (last >= 0)) (PreH4 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH6 : (last <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (z <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (last >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (z >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH15 : (n_pre = (Zlength (g)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 100000)) (PreH18 : ((Zlength (rows)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH20 : (0 <= z)) (PreH21 : (z < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH24 : ((-1) <= last)) (PreH25 : (last < 26)) (PreH26 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH27 : ((Zlength (next_l)) = 26)) (PreH28 : ((Zlength (prev_l)) = 26)) (PreH29 : ((Zlength (used_l)) = 26)) (PreH30 : ((Zlength (seen_l)) = 26)) (PreH31 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH32 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH33 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH34 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH35 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  ((( &( "c" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_22 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) <> last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0)) (PreH3 : ((Znth last next_l 0) < 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l)) = 26)) (PreH29 : ((Zlength (prev_l)) = 26)) (PreH30 : ((Zlength (used_l)) = 26)) (PreH31 : ((Zlength (seen_l)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  ((( &( "c" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_23 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) <> last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0)) (PreH3 : ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH4 : ((Znth last next_l 0) >= 0)) (PreH5 : (last >= 0)) (PreH6 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH7 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH8 : (last <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (z <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (last >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (z >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH17 : (n_pre = (Zlength (g)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (rows)) = n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH22 : (0 <= z)) (PreH23 : (z < n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH26 : ((-1) <= last)) (PreH27 : (last < 26)) (PreH28 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH29 : ((Zlength (next_l)) = 26)) (PreH30 : ((Zlength (prev_l)) = 26)) (PreH31 : ((Zlength (used_l)) = 26)) (PreH32 : ((Zlength (seen_l)) = 26)) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH34 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH35 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH36 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH37 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  ((( &( "c" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_24 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0)) (PreH3 : ((Znth last next_l 0) < 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l)) = 26)) (PreH29 : ((Zlength (prev_l)) = 26)) (PreH30 : ((Zlength (used_l)) = 26)) (PreH31 : ((Zlength (seen_l)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l)) )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0)) (PreH3 : ((Znth last next_l 0) < 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l)) = 26)) (PreH29 : ((Zlength (prev_l)) = 26)) (PreH30 : ((Zlength (used_l)) = 26)) (PreH31 : ((Zlength (seen_l)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l)) )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition solver_safety_wit_24_split_goal_1 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0)) (PreH3 : ((Znth last next_l 0) < 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l)) = 26)) (PreH29 : ((Zlength (prev_l)) = 26)) (PreH30 : ((Zlength (used_l)) = 26)) (PreH31 : ((Zlength (seen_l)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l)) )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_24_split_goal_2 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0)) (PreH3 : ((Znth last next_l 0) < 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l)) = 26)) (PreH29 : ((Zlength (prev_l)) = 26)) (PreH30 : ((Zlength (used_l)) = 26)) (PreH31 : ((Zlength (seen_l)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l)) )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_25 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0)) (PreH3 : ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH4 : ((Znth last next_l 0) >= 0)) (PreH5 : (last >= 0)) (PreH6 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH7 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH8 : (last <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (z <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (last >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (z >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH17 : (n_pre = (Zlength (g)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (rows)) = n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH22 : (0 <= z)) (PreH23 : (z < n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH26 : ((-1) <= last)) (PreH27 : (last < 26)) (PreH28 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH29 : ((Zlength (next_l)) = 26)) (PreH30 : ((Zlength (prev_l)) = 26)) (PreH31 : ((Zlength (used_l)) = 26)) (PreH32 : ((Zlength (seen_l)) = 26)) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH34 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH35 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH36 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH37 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l)) )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0)) (PreH3 : ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH4 : ((Znth last next_l 0) >= 0)) (PreH5 : (last >= 0)) (PreH6 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH7 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH8 : (last <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (z <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (last >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (z >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH17 : (n_pre = (Zlength (g)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (rows)) = n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH22 : (0 <= z)) (PreH23 : (z < n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH26 : ((-1) <= last)) (PreH27 : (last < 26)) (PreH28 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH29 : ((Zlength (next_l)) = 26)) (PreH30 : ((Zlength (prev_l)) = 26)) (PreH31 : ((Zlength (used_l)) = 26)) (PreH32 : ((Zlength (seen_l)) = 26)) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH34 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH35 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH36 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH37 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l)) )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition solver_safety_wit_25_split_goal_1 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0)) (PreH3 : ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH4 : ((Znth last next_l 0) >= 0)) (PreH5 : (last >= 0)) (PreH6 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH7 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH8 : (last <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (z <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (last >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (z >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH17 : (n_pre = (Zlength (g)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (rows)) = n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH22 : (0 <= z)) (PreH23 : (z < n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH26 : ((-1) <= last)) (PreH27 : (last < 26)) (PreH28 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH29 : ((Zlength (next_l)) = 26)) (PreH30 : ((Zlength (prev_l)) = 26)) (PreH31 : ((Zlength (used_l)) = 26)) (PreH32 : ((Zlength (seen_l)) = 26)) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH34 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH35 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH36 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH37 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l)) )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_25_split_goal_2 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0)) (PreH3 : ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH4 : ((Znth last next_l 0) >= 0)) (PreH5 : (last >= 0)) (PreH6 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH7 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH8 : (last <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (z <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (last >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (z >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH17 : (n_pre = (Zlength (g)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (rows)) = n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH22 : (0 <= z)) (PreH23 : (z < n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH26 : ((-1) <= last)) (PreH27 : (last < 26)) (PreH28 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH29 : ((Zlength (next_l)) = 26)) (PreH30 : ((Zlength (prev_l)) = 26)) (PreH31 : ((Zlength (used_l)) = 26)) (PreH32 : ((Zlength (seen_l)) = 26)) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH34 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH35 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH36 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH37 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l)) )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_26 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) < 0)) (PreH2 : ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : ((Znth last next_l 0) >= 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l)) = 26)) (PreH29 : ((Zlength (prev_l)) = 26)) (PreH30 : ((Zlength (used_l)) = 26)) (PreH31 : ((Zlength (seen_l)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l)) )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) < 0)) (PreH2 : ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : ((Znth last next_l 0) >= 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l)) = 26)) (PreH29 : ((Zlength (prev_l)) = 26)) (PreH30 : ((Zlength (used_l)) = 26)) (PreH31 : ((Zlength (seen_l)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l)) )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition solver_safety_wit_26_split_goal_1 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) < 0)) (PreH2 : ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : ((Znth last next_l 0) >= 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l)) = 26)) (PreH29 : ((Zlength (prev_l)) = 26)) (PreH30 : ((Zlength (used_l)) = 26)) (PreH31 : ((Zlength (seen_l)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l)) )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_26_split_goal_2 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) < 0)) (PreH2 : ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : ((Znth last next_l 0) >= 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l)) = 26)) (PreH29 : ((Zlength (prev_l)) = 26)) (PreH30 : ((Zlength (used_l)) = 26)) (PreH31 : ((Zlength (seen_l)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l)) )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_27 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) < 0)) (PreH2 : ((Znth last next_l 0) < 0)) (PreH3 : (last >= 0)) (PreH4 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH6 : (last <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (z <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (last >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (z >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH15 : (n_pre = (Zlength (g)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 100000)) (PreH18 : ((Zlength (rows)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH20 : (0 <= z)) (PreH21 : (z < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH24 : ((-1) <= last)) (PreH25 : (last < 26)) (PreH26 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH27 : ((Zlength (next_l)) = 26)) (PreH28 : ((Zlength (prev_l)) = 26)) (PreH29 : ((Zlength (used_l)) = 26)) (PreH30 : ((Zlength (seen_l)) = 26)) (PreH31 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH32 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH33 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH34 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH35 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l)) )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) < 0)) (PreH2 : ((Znth last next_l 0) < 0)) (PreH3 : (last >= 0)) (PreH4 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH6 : (last <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (z <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (last >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (z >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH15 : (n_pre = (Zlength (g)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 100000)) (PreH18 : ((Zlength (rows)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH20 : (0 <= z)) (PreH21 : (z < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH24 : ((-1) <= last)) (PreH25 : (last < 26)) (PreH26 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH27 : ((Zlength (next_l)) = 26)) (PreH28 : ((Zlength (prev_l)) = 26)) (PreH29 : ((Zlength (used_l)) = 26)) (PreH30 : ((Zlength (seen_l)) = 26)) (PreH31 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH32 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH33 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH34 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH35 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l)) )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition solver_safety_wit_27_split_goal_1 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) < 0)) (PreH2 : ((Znth last next_l 0) < 0)) (PreH3 : (last >= 0)) (PreH4 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH6 : (last <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (z <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (last >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (z >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH15 : (n_pre = (Zlength (g)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 100000)) (PreH18 : ((Zlength (rows)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH20 : (0 <= z)) (PreH21 : (z < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH24 : ((-1) <= last)) (PreH25 : (last < 26)) (PreH26 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH27 : ((Zlength (next_l)) = 26)) (PreH28 : ((Zlength (prev_l)) = 26)) (PreH29 : ((Zlength (used_l)) = 26)) (PreH30 : ((Zlength (seen_l)) = 26)) (PreH31 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH32 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH33 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH34 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH35 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l)) )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_27_split_goal_2 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) < 0)) (PreH2 : ((Znth last next_l 0) < 0)) (PreH3 : (last >= 0)) (PreH4 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH6 : (last <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (z <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (last >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (z >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH15 : (n_pre = (Zlength (g)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 100000)) (PreH18 : ((Zlength (rows)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH20 : (0 <= z)) (PreH21 : (z < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH24 : ((-1) <= last)) (PreH25 : (last < 26)) (PreH26 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH27 : ((Zlength (next_l)) = 26)) (PreH28 : ((Zlength (prev_l)) = 26)) (PreH29 : ((Zlength (used_l)) = 26)) (PreH30 : ((Zlength (seen_l)) = 26)) (PreH31 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH32 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH33 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH34 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH35 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l)) )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_28 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (last < 0)) (PreH2 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH4 : (last <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (z <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (last >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (z >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH13 : (n_pre = (Zlength (g)))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : ((Zlength (rows)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH18 : (0 <= z)) (PreH19 : (z < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH22 : ((-1) <= last)) (PreH23 : (last < 26)) (PreH24 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH25 : ((Zlength (next_l)) = 26)) (PreH26 : ((Zlength (prev_l)) = 26)) (PreH27 : ((Zlength (used_l)) = 26)) (PreH28 : ((Zlength (seen_l)) = 26)) (PreH29 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH30 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH31 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH32 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH33 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (last < 0)) (PreH2 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH4 : (last <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (z <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (last >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (z >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH13 : (n_pre = (Zlength (g)))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : ((Zlength (rows)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH18 : (0 <= z)) (PreH19 : (z < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH22 : ((-1) <= last)) (PreH23 : (last < 26)) (PreH24 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH25 : ((Zlength (next_l)) = 26)) (PreH26 : ((Zlength (prev_l)) = 26)) (PreH27 : ((Zlength (used_l)) = 26)) (PreH28 : ((Zlength (seen_l)) = 26)) (PreH29 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH30 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH31 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH32 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH33 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition solver_safety_wit_28_split_goal_1 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (last < 0)) (PreH2 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH4 : (last <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (z <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (last >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (z >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH13 : (n_pre = (Zlength (g)))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : ((Zlength (rows)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH18 : (0 <= z)) (PreH19 : (z < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH22 : ((-1) <= last)) (PreH23 : (last < 26)) (PreH24 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH25 : ((Zlength (next_l)) = 26)) (PreH26 : ((Zlength (prev_l)) = 26)) (PreH27 : ((Zlength (used_l)) = 26)) (PreH28 : ((Zlength (seen_l)) = 26)) (PreH29 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH30 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH31 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH32 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH33 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_28_split_goal_2 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (last < 0)) (PreH2 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH4 : (last <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (z <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (last >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (z >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH13 : (n_pre = (Zlength (g)))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : ((Zlength (rows)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH18 : (0 <= z)) (PreH19 : (z < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH22 : ((-1) <= last)) (PreH23 : (last < 26)) (PreH24 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH25 : ((Zlength (next_l)) = 26)) (PreH26 : ((Zlength (prev_l)) = 26)) (PreH27 : ((Zlength (used_l)) = 26)) (PreH28 : ((Zlength (seen_l)) = 26)) (PreH29 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH30 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH31 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH32 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH33 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_29 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l: (@list Z)) (prev_l: (@list Z)) (used_l: (@list Z)) (seen_l: (@list Z)) (z: Z) (last: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : ((-1) <= last)) (PreH10 : (last < 26)) (PreH11 : ((Zlength (next_l)) = 26)) (PreH12 : ((Zlength (prev_l)) = 26)) (PreH13 : ((Zlength (used_l)) = 26)) (PreH14 : ((Zlength (seen_l)) = 26)) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH17 : (GraphBuildState g (z + 1 ) next_l prev_l used_l )) ,
  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
|--
  “ ((z + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (z + 1 )) ”
.

Definition solver_safety_wit_30 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (z: Z) (PreH1 : (z >= n_pre)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH7 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (next_l)) = 26)) (PreH11 : ((Zlength (prev_l)) = 26)) (PreH12 : ((Zlength (used_l)) = 26)) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH14 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH15 : (GraphBuildState g z next_l prev_l used_l )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  (IntArray.full ( &( "visited" ) ) 26 (repeat_Z (0) (26)) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_31 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (z: Z) (PreH1 : (z >= n_pre)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH7 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (next_l)) = 26)) (PreH11 : ((Zlength (prev_l)) = 26)) (PreH12 : ((Zlength (used_l)) = 26)) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH14 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH15 : (GraphBuildState g z next_l prev_l used_l )) ,
  ((( &( "start" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  (IntArray.full ( &( "visited" ) ) 26 (repeat_Z (0) (26)) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_32 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (start: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : (0 <= start)) (PreH6 : (start <= 26)) (PreH7 : (0 <= len)) (PreH8 : (len <= 26)) (PreH9 : ((Zlength (output_l)) = len)) (PreH10 : ((Zlength (next_l)) = 26)) (PreH11 : ((Zlength (prev_l)) = 26)) (PreH12 : ((Zlength (used_l)) = 26)) (PreH13 : ((Zlength (visited_l)) = 26)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH16 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH17 : (TraversalState next_l prev_l used_l start visited_l output_l )) ,
  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ (26 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 26) ”
.

Definition solver_safety_wit_33 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (start: Z) (PreH1 : ((Znth start used_l 0) <> 0)) (PreH2 : (start < 26)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start <= 26)) (PreH9 : (0 <= len)) (PreH10 : (len <= 26)) (PreH11 : ((Zlength (output_l)) = len)) (PreH12 : ((Zlength (next_l)) = 26)) (PreH13 : ((Zlength (prev_l)) = 26)) (PreH14 : ((Zlength (used_l)) = 26)) (PreH15 : ((Zlength (visited_l)) = 26)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH18 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH19 : (TraversalState next_l prev_l used_l start visited_l output_l )) ,
  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_34 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : (0 <= start)) (PreH6 : (start < 26)) (PreH7 : ((-1) <= c)) (PreH8 : (c < 26)) (PreH9 : (0 <= len)) (PreH10 : (len <= 26)) (PreH11 : ((Zlength (output_l)) = len)) (PreH12 : ((Zlength (next_l)) = 26)) (PreH13 : ((Zlength (prev_l)) = 26)) (PreH14 : ((Zlength (used_l)) = 26)) (PreH15 : ((Zlength (visited_l)) = 26)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH18 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH19 : (PathScanState next_l prev_l used_l start c visited_l output_l )) ,
  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_35 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : ((Znth c visited_l 0) = 0)) (PreH2 : (c >= 0)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start < 26)) (PreH9 : ((-1) <= c)) (PreH10 : (c < 26)) (PreH11 : (0 <= len)) (PreH12 : (len <= 26)) (PreH13 : ((Zlength (output_l)) = len)) (PreH14 : ((Zlength (next_l)) = 26)) (PreH15 : ((Zlength (prev_l)) = 26)) (PreH16 : ((Zlength (used_l)) = 26)) (PreH17 : ((Zlength (visited_l)) = 26)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH20 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH21 : (PathScanState next_l prev_l used_l start c visited_l output_l )) ,
  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_36 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : ((Znth c visited_l 0) = 0)) (PreH2 : (c >= 0)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start < 26)) (PreH9 : ((-1) <= c)) (PreH10 : (c < 26)) (PreH11 : (0 <= len)) (PreH12 : (len <= 26)) (PreH13 : ((Zlength (output_l)) = len)) (PreH14 : ((Zlength (next_l)) = 26)) (PreH15 : ((Zlength (prev_l)) = 26)) (PreH16 : ((Zlength (used_l)) = 26)) (PreH17 : ((Zlength (visited_l)) = 26)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH20 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH21 : (PathScanState next_l prev_l used_l start c visited_l output_l )) ,
  (IntArray.full ( &( "visited" ) ) 26 (replace_Znth (c) (1) (visited_l)) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ ((97 + c ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (97 + c )) ”
.

Definition solver_safety_wit_37 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : ((Znth c visited_l 0) = 0)) (PreH2 : (c >= 0)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start < 26)) (PreH9 : ((-1) <= c)) (PreH10 : (c < 26)) (PreH11 : (0 <= len)) (PreH12 : (len <= 26)) (PreH13 : ((Zlength (output_l)) = len)) (PreH14 : ((Zlength (next_l)) = 26)) (PreH15 : ((Zlength (prev_l)) = 26)) (PreH16 : ((Zlength (used_l)) = 26)) (PreH17 : ((Zlength (visited_l)) = 26)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH20 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH21 : (PathScanState next_l prev_l used_l start c visited_l output_l )) ,
  (IntArray.full ( &( "visited" ) ) 26 (replace_Znth (c) (1) (visited_l)) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solver_safety_wit_38 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : ((Znth c visited_l 0) = 0)) (PreH2 : (c >= 0)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start < 26)) (PreH9 : ((-1) <= c)) (PreH10 : (c < 26)) (PreH11 : (0 <= len)) (PreH12 : (len <= 26)) (PreH13 : ((Zlength (output_l)) = len)) (PreH14 : ((Zlength (next_l)) = 26)) (PreH15 : ((Zlength (prev_l)) = 26)) (PreH16 : ((Zlength (used_l)) = 26)) (PreH17 : ((Zlength (visited_l)) = 26)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH20 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH21 : (PathScanState next_l prev_l used_l start c visited_l output_l )) ,
  (CharArray.seg out_pre 0 (len + 1 ) (app (output_l) ((cons ((97 + c )) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (len + 1 ) 64 )
  **  (IntArray.full ( &( "visited" ) ) 26 (replace_Znth (c) (1) (visited_l)) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
|--
  “ ((len + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (len + 1 )) ”
.

Definition solver_safety_wit_39 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l: (@list Z)) (prev_l: (@list Z)) (used_l: (@list Z)) (visited_l: (@list Z)) (output_l: (@list Z)) (start: Z) (c: Z) (len: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : (0 <= start)) (PreH6 : (start < 26)) (PreH7 : ((-1) <= c)) (PreH8 : (c < 26)) (PreH9 : (0 <= len)) (PreH10 : (len <= 26)) (PreH11 : ((Zlength (output_l)) = len)) (PreH12 : ((Zlength (next_l)) = 26)) (PreH13 : ((Zlength (prev_l)) = 26)) (PreH14 : ((Zlength (used_l)) = 26)) (PreH15 : ((Zlength (visited_l)) = 26)) (PreH16 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH17 : (TraversalState next_l prev_l used_l (start + 1 ) visited_l output_l )) ,
  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ ((start + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (start + 1 )) ”
.

Definition solver_safety_wit_40 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (start: Z) (PreH1 : ((Znth start used_l 0) = 0)) (PreH2 : (start < 26)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start <= 26)) (PreH9 : (0 <= len)) (PreH10 : (len <= 26)) (PreH11 : ((Zlength (output_l)) = len)) (PreH12 : ((Zlength (next_l)) = 26)) (PreH13 : ((Zlength (prev_l)) = 26)) (PreH14 : ((Zlength (used_l)) = 26)) (PreH15 : ((Zlength (visited_l)) = 26)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH18 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH19 : (TraversalState next_l prev_l used_l start visited_l output_l )) ,
  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ ((start + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (start + 1 )) ”
.

Definition solver_safety_wit_41 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (start: Z) (PreH1 : ((Znth start prev_l 0) >= 0)) (PreH2 : ((Znth start used_l 0) <> 0)) (PreH3 : (start < 26)) (PreH4 : (n_pre = (Zlength (g)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= start)) (PreH9 : (start <= 26)) (PreH10 : (0 <= len)) (PreH11 : (len <= 26)) (PreH12 : ((Zlength (output_l)) = len)) (PreH13 : ((Zlength (next_l)) = 26)) (PreH14 : ((Zlength (prev_l)) = 26)) (PreH15 : ((Zlength (used_l)) = 26)) (PreH16 : ((Zlength (visited_l)) = 26)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH19 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH20 : (TraversalState next_l prev_l used_l start visited_l output_l )) ,
  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ ((start + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (start + 1 )) ”
.

Definition solver_safety_wit_42 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (start: Z) (PreH1 : (start >= 26)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= start)) (PreH7 : (start <= 26)) (PreH8 : (0 <= len)) (PreH9 : (len <= 26)) (PreH10 : ((Zlength (output_l)) = len)) (PreH11 : ((Zlength (next_l)) = 26)) (PreH12 : ((Zlength (prev_l)) = 26)) (PreH13 : ((Zlength (used_l)) = 26)) (PreH14 : ((Zlength (visited_l)) = 26)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH17 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH18 : (TraversalState next_l prev_l used_l start visited_l output_l )) ,
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_43 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (c: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : (0 <= c)) (PreH6 : (c <= 26)) (PreH7 : (0 <= len)) (PreH8 : (len <= 26)) (PreH9 : ((Zlength (output_l)) = len)) (PreH10 : ((Zlength (next_l)) = 26)) (PreH11 : ((Zlength (prev_l)) = 26)) (PreH12 : ((Zlength (used_l)) = 26)) (PreH13 : ((Zlength (visited_l)) = 26)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH16 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH17 : (TraversalState next_l prev_l used_l 26 visited_l output_l )) (PreH18 : (CoverageScanState used_l visited_l c )) ,
  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ (26 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 26) ”
.

Definition solver_safety_wit_44 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (c: Z) (PreH1 : ((Znth c visited_l 0) = 0)) (PreH2 : ((Znth c used_l 0) <> 0)) (PreH3 : (c < 26)) (PreH4 : (n_pre = (Zlength (g)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c <= 26)) (PreH10 : (0 <= len)) (PreH11 : (len <= 26)) (PreH12 : ((Zlength (output_l)) = len)) (PreH13 : ((Zlength (next_l)) = 26)) (PreH14 : ((Zlength (prev_l)) = 26)) (PreH15 : ((Zlength (used_l)) = 26)) (PreH16 : ((Zlength (visited_l)) = 26)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH19 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH20 : (TraversalState next_l prev_l used_l 26 visited_l output_l )) (PreH21 : (CoverageScanState used_l visited_l c )) ,
  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_45 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (c: Z) (PreH1 : ((Znth c used_l 0) = 0)) (PreH2 : (c < 26)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c <= 26)) (PreH9 : (0 <= len)) (PreH10 : (len <= 26)) (PreH11 : ((Zlength (output_l)) = len)) (PreH12 : ((Zlength (next_l)) = 26)) (PreH13 : ((Zlength (prev_l)) = 26)) (PreH14 : ((Zlength (used_l)) = 26)) (PreH15 : ((Zlength (visited_l)) = 26)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH18 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH19 : (TraversalState next_l prev_l used_l 26 visited_l output_l )) (PreH20 : (CoverageScanState used_l visited_l c )) ,
  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ ((c + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c + 1 )) ”
.

Definition solver_safety_wit_46 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (c: Z) (PreH1 : ((Znth c visited_l 0) <> 0)) (PreH2 : ((Znth c used_l 0) <> 0)) (PreH3 : (c < 26)) (PreH4 : (n_pre = (Zlength (g)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c <= 26)) (PreH10 : (0 <= len)) (PreH11 : (len <= 26)) (PreH12 : ((Zlength (output_l)) = len)) (PreH13 : ((Zlength (next_l)) = 26)) (PreH14 : ((Zlength (prev_l)) = 26)) (PreH15 : ((Zlength (used_l)) = 26)) (PreH16 : ((Zlength (visited_l)) = 26)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH19 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH20 : (TraversalState next_l prev_l used_l 26 visited_l output_l )) (PreH21 : (CoverageScanState used_l visited_l c )) ,
  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ ((c + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c + 1 )) ”
.

Definition solver_safety_wit_47 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l: (@list Z)) (prev_l: (@list Z)) (used_l: (@list Z)) (visited_l: (@list Z)) (output_l: (@list Z)) (len: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : (0 <= len)) (PreH6 : (len <= 26)) (PreH7 : ((Zlength (output_l)) = len)) (PreH8 : (SuccessfulTraversal g next_l prev_l used_l visited_l output_l )) ,
  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_48 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l: (@list Z)) (prev_l: (@list Z)) (used_l: (@list Z)) (visited_l: (@list Z)) (output_l: (@list Z)) (len: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : (0 <= len)) (PreH6 : (len <= 26)) (PreH7 : ((Zlength (output_l)) = len)) (PreH8 : (SuccessfulTraversal g next_l prev_l used_l visited_l output_l )) ,
  (CharArray.seg out_pre 0 (len + 1 ) (app (output_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (len + 1 ) 64 )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (PreH1 : (Pre g )) (PreH2 : (1 <= (Zlength (g)))) (PreH3 : ((Zlength (g)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (g)))) -> ((0 < (Zlength ((Znth (i) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (i) (g) ((@nil Z))))) <= 100000)))) (PreH5 : forall (i_2: Z) , forall (j: Z) , (((((0 <= i_2) /\ (i_2 < (Zlength (g)))) /\ (0 <= j)) /\ (j < (Zlength ((Znth (i_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (j) ((Znth (i_2) (g) ((@nil Z)))) (0))) /\ ((Znth (j) ((Znth (i_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH6 : (n_pre = (Zlength (g)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((((Znth (i_3) (rows) ((@nil Z))) = (c_string ((Znth (i_3) (g) ((@nil Z)))))) /\ (valid_string (Znth (i_3) (g) ((@nil Z))) )) /\ ((string_length ((Znth (i_3) (g) ((@nil Z))))) < INT_MAX)))) ,
  (IntArray.full ( &( "used" ) ) 26 (repeat_Z (0) (26)) )
  **  (IntArray.undef_full ( &( "prev" ) ) 26 )
  **  (IntArray.undef_full ( &( "next" ) ) 26 )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
|--
  EX (used_l: (@list Z))  (prev_prefix: (@list Z))  (next_prefix: (@list Z)) ,
  “ (Pre g ) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 26) ” 
  &&  “ ((Zlength (next_prefix)) = 0) ” 
  &&  “ ((Zlength (prev_prefix)) = 0) ” 
  &&  “ (InitState next_prefix prev_prefix used_l ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.seg ( &( "next" ) ) 0 0 next_prefix )
  **  (IntArray.undef_seg ( &( "next" ) ) 0 26 )
  **  (IntArray.seg ( &( "prev" ) ) 0 0 prev_prefix )
  **  (IntArray.undef_seg ( &( "prev" ) ) 0 26 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (PreH1 : (Pre g )) (PreH2 : (1 <= (Zlength (g)))) (PreH3 : ((Zlength (g)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (g)))) -> ((0 < (Zlength ((Znth (i) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (i) (g) ((@nil Z))))) <= 100000)))) (PreH5 : forall (i_2: Z) , forall (j: Z) , (((((0 <= i_2) /\ (i_2 < (Zlength (g)))) /\ (0 <= j)) /\ (j < (Zlength ((Znth (i_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (j) ((Znth (i_2) (g) ((@nil Z)))) (0))) /\ ((Znth (j) ((Znth (i_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH6 : (n_pre = (Zlength (g)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((((Znth (i_3) (rows) ((@nil Z))) = (c_string ((Znth (i_3) (g) ((@nil Z)))))) /\ (valid_string (Znth (i_3) (g) ((@nil Z))) )) /\ ((string_length ((Znth (i_3) (g) ((@nil Z))))) < INT_MAX)))) ,
  TT && emp 
|--
  “ (InitState (@nil Z) (@nil Z) (repeat_Z (0) (26)) ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (PreH1 : (Pre g )) (PreH2 : (1 <= (Zlength (g)))) (PreH3 : ((Zlength (g)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (g)))) -> ((0 < (Zlength ((Znth (i) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (i) (g) ((@nil Z))))) <= 100000)))) (PreH5 : forall (i_2: Z) , forall (j: Z) , (((((0 <= i_2) /\ (i_2 < (Zlength (g)))) /\ (0 <= j)) /\ (j < (Zlength ((Znth (i_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (j) ((Znth (i_2) (g) ((@nil Z)))) (0))) /\ ((Znth (j) ((Znth (i_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH6 : (n_pre = (Zlength (g)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((((Znth (i_3) (rows) ((@nil Z))) = (c_string ((Znth (i_3) (g) ((@nil Z)))))) /\ (valid_string (Znth (i_3) (g) ((@nil Z))) )) /\ ((string_length ((Znth (i_3) (g) ((@nil Z))))) < INT_MAX)))) ,
  (InitState (@nil Z) (@nil Z) (repeat_Z (0) (26)) )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (PreH1 : (Pre g )) (PreH2 : (1 <= (Zlength (g)))) (PreH3 : ((Zlength (g)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (g)))) -> ((0 < (Zlength ((Znth (i) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (i) (g) ((@nil Z))))) <= 100000)))) (PreH5 : forall (i_2: Z) , forall (j: Z) , (((((0 <= i_2) /\ (i_2 < (Zlength (g)))) /\ (0 <= j)) /\ (j < (Zlength ((Znth (i_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (j) ((Znth (i_2) (g) ((@nil Z)))) (0))) /\ ((Znth (j) ((Znth (i_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH6 : (n_pre = (Zlength (g)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((((Znth (i_3) (rows) ((@nil Z))) = (c_string ((Znth (i_3) (g) ((@nil Z)))))) /\ (valid_string (Znth (i_3) (g) ((@nil Z))) )) /\ ((string_length ((Znth (i_3) (g) ((@nil Z))))) < INT_MAX)))) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (PreH1 : (Pre g )) (PreH2 : (1 <= (Zlength (g)))) (PreH3 : ((Zlength (g)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (g)))) -> ((0 < (Zlength ((Znth (i) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (i) (g) ((@nil Z))))) <= 100000)))) (PreH5 : forall (i_2: Z) , forall (j: Z) , (((((0 <= i_2) /\ (i_2 < (Zlength (g)))) /\ (0 <= j)) /\ (j < (Zlength ((Znth (i_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (j) ((Znth (i_2) (g) ((@nil Z)))) (0))) /\ ((Znth (j) ((Znth (i_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH6 : (n_pre = (Zlength (g)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((((Znth (i_3) (rows) ((@nil Z))) = (c_string ((Znth (i_3) (g) ((@nil Z)))))) /\ (valid_string (Znth (i_3) (g) ((@nil Z))) )) /\ ((string_length ((Znth (i_3) (g) ((@nil Z))))) < INT_MAX)))) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition solver_entail_wit_1_split_goal_4 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (PreH1 : (Pre g )) (PreH2 : (1 <= (Zlength (g)))) (PreH3 : ((Zlength (g)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (g)))) -> ((0 < (Zlength ((Znth (i) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (i) (g) ((@nil Z))))) <= 100000)))) (PreH5 : forall (i_2: Z) , forall (j: Z) , (((((0 <= i_2) /\ (i_2 < (Zlength (g)))) /\ (0 <= j)) /\ (j < (Zlength ((Znth (i_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (j) ((Znth (i_2) (g) ((@nil Z)))) (0))) /\ ((Znth (j) ((Znth (i_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH6 : (n_pre = (Zlength (g)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((((Znth (i_3) (rows) ((@nil Z))) = (c_string ((Znth (i_3) (g) ((@nil Z)))))) /\ (valid_string (Znth (i_3) (g) ((@nil Z))) )) /\ ((string_length ((Znth (i_3) (g) ((@nil Z))))) < INT_MAX)))) ,
  forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))
.

Definition solver_entail_wit_1_split_goal_5 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (PreH1 : (Pre g )) (PreH2 : (1 <= (Zlength (g)))) (PreH3 : ((Zlength (g)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (g)))) -> ((0 < (Zlength ((Znth (i) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (i) (g) ((@nil Z))))) <= 100000)))) (PreH5 : forall (i_2: Z) , forall (j: Z) , (((((0 <= i_2) /\ (i_2 < (Zlength (g)))) /\ (0 <= j)) /\ (j < (Zlength ((Znth (i_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (j) ((Znth (i_2) (g) ((@nil Z)))) (0))) /\ ((Znth (j) ((Znth (i_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH6 : (n_pre = (Zlength (g)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((((Znth (i_3) (rows) ((@nil Z))) = (c_string ((Znth (i_3) (g) ((@nil Z)))))) /\ (valid_string (Znth (i_3) (g) ((@nil Z))) )) /\ ((string_length ((Znth (i_3) (g) ((@nil Z))))) < INT_MAX)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))
.

Definition solver_entail_wit_2 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_prefix_2: (@list Z)) (next_prefix_2: (@list Z)) (i: Z) (PreH1 : (i < 26)) (PreH2 : (Pre g )) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= i)) (PreH10 : (i <= 26)) (PreH11 : ((Zlength (next_prefix_2)) = i)) (PreH12 : ((Zlength (prev_prefix_2)) = i)) (PreH13 : (InitState next_prefix_2 prev_prefix_2 used_l_2 )) ,
  (IntArray.seg ( &( "next" ) ) 0 (i + 1 ) (app (next_prefix_2) ((cons ((-1)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "next" ) ) (i + 1 ) 26 )
  **  (IntArray.seg ( &( "prev" ) ) 0 (i + 1 ) (app (prev_prefix_2) ((cons ((-1)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "prev" ) ) (i + 1 ) 26 )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l_2 )
|--
  EX (used_l: (@list Z))  (prev_prefix: (@list Z))  (next_prefix: (@list Z)) ,
  “ (Pre g ) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 26) ” 
  &&  “ ((Zlength (next_prefix)) = (i + 1 )) ” 
  &&  “ ((Zlength (prev_prefix)) = (i + 1 )) ” 
  &&  “ (InitState next_prefix prev_prefix used_l ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.seg ( &( "next" ) ) 0 (i + 1 ) next_prefix )
  **  (IntArray.undef_seg ( &( "next" ) ) (i + 1 ) 26 )
  **  (IntArray.seg ( &( "prev" ) ) 0 (i + 1 ) prev_prefix )
  **  (IntArray.undef_seg ( &( "prev" ) ) (i + 1 ) 26 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_prefix_2: (@list Z)) (next_prefix_2: (@list Z)) (i: Z) (PreH1 : (i < 26)) (PreH2 : (Pre g )) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= i)) (PreH10 : (i <= 26)) (PreH11 : ((Zlength (next_prefix_2)) = i)) (PreH12 : ((Zlength (prev_prefix_2)) = i)) (PreH13 : (InitState next_prefix_2 prev_prefix_2 used_l_2 )) ,
  TT && emp 
|--
  “ (InitState (app (next_prefix_2) ((cons ((-1)) ((@nil Z))))) (app (prev_prefix_2) ((cons ((-1)) ((@nil Z))))) used_l_2 ) ” 
  &&  “ ((Zlength ((app (prev_prefix_2) ((cons ((-1)) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ ((Zlength ((app (next_prefix_2) ((cons ((-1)) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_prefix_2: (@list Z)) (next_prefix_2: (@list Z)) (i: Z) (PreH1 : (i < 26)) (PreH2 : (Pre g )) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= i)) (PreH10 : (i <= 26)) (PreH11 : ((Zlength (next_prefix_2)) = i)) (PreH12 : ((Zlength (prev_prefix_2)) = i)) (PreH13 : (InitState next_prefix_2 prev_prefix_2 used_l_2 )) ,
  (InitState (app (next_prefix_2) ((cons ((-1)) ((@nil Z))))) (app (prev_prefix_2) ((cons ((-1)) ((@nil Z))))) used_l_2 )
.

Definition solver_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_prefix_2: (@list Z)) (next_prefix_2: (@list Z)) (i: Z) (PreH1 : (i < 26)) (PreH2 : (Pre g )) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= i)) (PreH10 : (i <= 26)) (PreH11 : ((Zlength (next_prefix_2)) = i)) (PreH12 : ((Zlength (prev_prefix_2)) = i)) (PreH13 : (InitState next_prefix_2 prev_prefix_2 used_l_2 )) ,
  ((Zlength ((app (prev_prefix_2) ((cons ((-1)) ((@nil Z))))))) = (i + 1 ))
.

Definition solver_entail_wit_2_split_goal_3 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_prefix_2: (@list Z)) (next_prefix_2: (@list Z)) (i: Z) (PreH1 : (i < 26)) (PreH2 : (Pre g )) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= i)) (PreH10 : (i <= 26)) (PreH11 : ((Zlength (next_prefix_2)) = i)) (PreH12 : ((Zlength (prev_prefix_2)) = i)) (PreH13 : (InitState next_prefix_2 prev_prefix_2 used_l_2 )) ,
  ((Zlength ((app (next_prefix_2) ((cons ((-1)) ((@nil Z))))))) = (i + 1 ))
.

Definition solver_entail_wit_3 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_prefix: (@list Z)) (next_prefix: (@list Z)) (i: Z) (PreH1 : (i >= 26)) (PreH2 : (Pre g )) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= i)) (PreH10 : (i <= 26)) (PreH11 : ((Zlength (next_prefix)) = i)) (PreH12 : ((Zlength (prev_prefix)) = i)) (PreH13 : (InitState next_prefix prev_prefix used_l_2 )) ,
  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.seg ( &( "next" ) ) 0 i next_prefix )
  **  (IntArray.undef_seg ( &( "next" ) ) i 26 )
  **  (IntArray.seg ( &( "prev" ) ) 0 i prev_prefix )
  **  (IntArray.undef_seg ( &( "prev" ) ) i 26 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l_2 )
|--
  EX (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g 0 next_l prev_l used_l ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_prefix: (@list Z)) (next_prefix: (@list Z)) (i: Z) (PreH1 : (i >= 26)) (PreH2 : (Pre g )) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= i)) (PreH10 : (i <= 26)) (PreH11 : ((Zlength (next_prefix)) = i)) (PreH12 : ((Zlength (prev_prefix)) = i)) (PreH13 : (InitState next_prefix prev_prefix used_l_2 )) ,
  (IntArray.seg ( &( "next" ) ) 0 i next_prefix )
  **  (IntArray.seg ( &( "prev" ) ) 0 i prev_prefix )
|--
  EX (prev_l: (@list Z))  (next_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l_2)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g 0 next_l prev_l used_l_2 ) ”
  &&  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
).

Definition solver_entail_wit_4 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (z: Z) (PreH1 : (z < n_pre)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH7 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (next_l_2)) = 26)) (PreH11 : ((Zlength (prev_l_2)) = 26)) (PreH12 : ((Zlength (used_l_2)) = 26)) (PreH13 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH14 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH15 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l_2 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l_2 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l_2 )
|--
  EX (row_ptr: Z)  (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g z next_l prev_l used_l ) ”
  &&  (CharPtrArray2.missing_i words_pre n_pre z row_ptr rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (z: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth z rows __default__List_Z))))) (PreH2 : (z < n_pre)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= z)) (PreH10 : (z <= n_pre)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH15 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH16 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth z rows __default__List_Z))) (Znth z rows __default__List_Z) )
|--
  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26))) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ”
  &&  (CharArray.full row_ptr_2 ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (z: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth z rows __default__List_Z))))) (PreH2 : (z < n_pre)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= z)) (PreH10 : (z <= n_pre)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH15 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH16 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth z rows __default__List_Z))) (Znth z rows __default__List_Z) )
|--
  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26))) ”
.

Definition solver_entail_wit_4_split_goal_2 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (z: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth z rows __default__List_Z))))) (PreH2 : (z < n_pre)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= z)) (PreH10 : (z <= n_pre)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH15 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH16 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth z rows __default__List_Z))) (Znth z rows __default__List_Z) )
|--
  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26))) ”
.

Definition solver_entail_wit_4_split_goal_3 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (z: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth z rows __default__List_Z))))) (PreH2 : (z < n_pre)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= z)) (PreH10 : (z <= n_pre)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH15 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH16 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth z rows __default__List_Z))) (Znth z rows __default__List_Z) )
|--
  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ”
.

Definition solver_entail_wit_4_split_goal_4 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (z: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth z rows __default__List_Z))))) (PreH2 : (z < n_pre)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= z)) (PreH10 : (z <= n_pre)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH15 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH16 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth z rows __default__List_Z))) (Znth z rows __default__List_Z) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ”
.

Definition solver_entail_wit_4_split_goal_spatial := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (z: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth z rows __default__List_Z))))) (PreH2 : (z < n_pre)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= z)) (PreH10 : (z <= n_pre)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH15 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH16 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth z rows __default__List_Z))) (Znth z rows __default__List_Z) )
|--
  (CharArray.full row_ptr_2 ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
.

Definition solver_entail_wit_5 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l_2: (@list Z)) (prev_l_2: (@list Z)) (used_l_2: (@list Z)) (row_ptr: Z) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : ((Zlength (next_l_2)) = 26)) (PreH10 : ((Zlength (prev_l_2)) = 26)) (PreH11 : ((Zlength (used_l_2)) = 26)) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH13 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH14 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  (IntArray.full ( &( "seen" ) ) 26 (repeat_Z (0) (26)) )
  **  (CharPtrArray2.missing_i words_pre n_pre z row_ptr rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l_2 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l_2 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l_2 )
|--
  EX (seen_l: (@list Z))  (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z 0 next_l prev_l used_l seen_l (-1) ) ”
  &&  (CharPtrArray2.missing_i words_pre n_pre z row_ptr rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l_2: (@list Z)) (prev_l_2: (@list Z)) (used_l_2: (@list Z)) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : ((Zlength (next_l_2)) = 26)) (PreH10 : ((Zlength (prev_l_2)) = 26)) (PreH11 : ((Zlength (used_l_2)) = 26)) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH13 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH14 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  TT && emp 
|--
  “ (WordScanState g z 0 next_l_2 prev_l_2 used_l_2 (repeat_Z (0) (26)) (-1) ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26))) ” 
  &&  “ ((Zlength ((repeat_Z (0) (26)))) = 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ (0 <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l_2: (@list Z)) (prev_l_2: (@list Z)) (used_l_2: (@list Z)) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : ((Zlength (next_l_2)) = 26)) (PreH10 : ((Zlength (prev_l_2)) = 26)) (PreH11 : ((Zlength (used_l_2)) = 26)) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH13 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH14 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  (WordScanState g z 0 next_l_2 prev_l_2 used_l_2 (repeat_Z (0) (26)) (-1) )
.

Definition solver_entail_wit_5_split_goal_2 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l_2: (@list Z)) (prev_l_2: (@list Z)) (used_l_2: (@list Z)) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : ((Zlength (next_l_2)) = 26)) (PreH10 : ((Zlength (prev_l_2)) = 26)) (PreH11 : ((Zlength (used_l_2)) = 26)) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH13 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH14 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))
.

Definition solver_entail_wit_5_split_goal_3 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l_2: (@list Z)) (prev_l_2: (@list Z)) (used_l_2: (@list Z)) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : ((Zlength (next_l_2)) = 26)) (PreH10 : ((Zlength (prev_l_2)) = 26)) (PreH11 : ((Zlength (used_l_2)) = 26)) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH13 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH14 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))
.

Definition solver_entail_wit_5_split_goal_4 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l_2: (@list Z)) (prev_l_2: (@list Z)) (used_l_2: (@list Z)) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : ((Zlength (next_l_2)) = 26)) (PreH10 : ((Zlength (prev_l_2)) = 26)) (PreH11 : ((Zlength (used_l_2)) = 26)) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH13 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH14 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  ((Zlength ((repeat_Z (0) (26)))) = 26)
.

Definition solver_entail_wit_5_split_goal_5 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l_2: (@list Z)) (prev_l_2: (@list Z)) (used_l_2: (@list Z)) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : ((Zlength (next_l_2)) = 26)) (PreH10 : ((Zlength (prev_l_2)) = 26)) (PreH11 : ((Zlength (used_l_2)) = 26)) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH13 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH14 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))
.

Definition solver_entail_wit_5_split_goal_6 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l_2: (@list Z)) (prev_l_2: (@list Z)) (used_l_2: (@list Z)) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : ((Zlength (next_l_2)) = 26)) (PreH10 : ((Zlength (prev_l_2)) = 26)) (PreH11 : ((Zlength (used_l_2)) = 26)) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH13 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH14 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  (0 <= (Zlength ((Znth (z) (g) ((@nil Z))))))
.

Definition solver_entail_wit_5_split_goal_7 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l_2: (@list Z)) (prev_l_2: (@list Z)) (used_l_2: (@list Z)) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : ((Zlength (next_l_2)) = 26)) (PreH10 : ((Zlength (prev_l_2)) = 26)) (PreH11 : ((Zlength (used_l_2)) = 26)) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH13 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH14 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))
.

Definition solver_entail_wit_6 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : (0 <= z)) (PreH7 : (z < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH10 : ((-1) <= last)) (PreH11 : (last < 26)) (PreH12 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH13 : ((Zlength (next_l)) = 26)) (PreH14 : ((Zlength (prev_l)) = 26)) (PreH15 : ((Zlength (used_l)) = 26)) (PreH16 : ((Zlength (seen_l)) = 26)) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH19 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH20 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "c" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
|--
  “ (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ (last <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (z <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (last >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (z >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 )) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z i next_l prev_l used_l seen_l last ) ” 
  &&  “ ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0) ”
  &&  ((( &( "c" ) )) # Int  |-> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "s" ) )) # Ptr  |-> saved_s)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : (last <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (z <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) <= INT_MAX)) (PreH6 : (last >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (z >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) >= INT_MIN)) (PreH11 : (n_pre = (Zlength (g)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH16 : (0 <= z)) (PreH17 : (z < n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH20 : ((-1) <= last)) (PreH21 : (last < 26)) (PreH22 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH23 : ((Zlength (next_l)) = 26)) (PreH24 : ((Zlength (prev_l)) = 26)) (PreH25 : ((Zlength (used_l)) = 26)) (PreH26 : ((Zlength (seen_l)) = 26)) (PreH27 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH28 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH29 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH30 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) ,
  TT && emp 
|--
  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : (last <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (z <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) <= INT_MAX)) (PreH6 : (last >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (z >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) >= INT_MIN)) (PreH11 : (n_pre = (Zlength (g)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH16 : (0 <= z)) (PreH17 : (z < n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH20 : ((-1) <= last)) (PreH21 : (last < 26)) (PreH22 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH23 : ((Zlength (next_l)) = 26)) (PreH24 : ((Zlength (prev_l)) = 26)) (PreH25 : ((Zlength (used_l)) = 26)) (PreH26 : ((Zlength (seen_l)) = 26)) (PreH27 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH28 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH29 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH30 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) ,
  (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)
.

Definition solver_entail_wit_6_split_goal_2 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : (last <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (z <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) <= INT_MAX)) (PreH6 : (last >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (z >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) >= INT_MIN)) (PreH11 : (n_pre = (Zlength (g)))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 100000)) (PreH14 : ((Zlength (rows)) = n_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH16 : (0 <= z)) (PreH17 : (z < n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH20 : ((-1) <= last)) (PreH21 : (last < 26)) (PreH22 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH23 : ((Zlength (next_l)) = 26)) (PreH24 : ((Zlength (prev_l)) = 26)) (PreH25 : ((Zlength (used_l)) = 26)) (PreH26 : ((Zlength (seen_l)) = 26)) (PreH27 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH28 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH29 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH30 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) ,
  (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))
.

Definition solver_entail_wit_7_1 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) >= 0)) (PreH3 : ((Znth last next_l_2 0) < 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l_2)) = 26)) (PreH29 : ((Zlength (prev_l_2)) = 26)) (PreH30 : ((Zlength (used_l_2)) = 26)) (PreH31 : ((Zlength (seen_l_2)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l_2)) )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l_2)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  EX (seen_l: (@list Z))  (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z (i + 1 ) next_l prev_l used_l seen_l ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) ) ”
  &&  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) >= 0)) (PreH3 : ((Znth last next_l_2 0) < 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l_2)) = 26)) (PreH29 : ((Zlength (prev_l_2)) = 26)) (PreH30 : ((Zlength (used_l_2)) = 26)) (PreH31 : ((Zlength (seen_l_2)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  TT && emp 
|--
  “ (WordScanState g z (i + 1 ) (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) ) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)))) = 26) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)))) = 26) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l_2)))) = 26) ” 
  &&  “ ((Zlength ((replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l_2)))) = 26) ” 
  &&  “ ((i + 1 ) <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_7_1_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) >= 0)) (PreH3 : ((Znth last next_l_2 0) < 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l_2)) = 26)) (PreH29 : ((Zlength (prev_l_2)) = 26)) (PreH30 : ((Zlength (used_l_2)) = 26)) (PreH31 : ((Zlength (seen_l_2)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  (WordScanState g z (i + 1 ) (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) )
.

Definition solver_entail_wit_7_1_split_goal_2 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) >= 0)) (PreH3 : ((Znth last next_l_2 0) < 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l_2)) = 26)) (PreH29 : ((Zlength (prev_l_2)) = 26)) (PreH30 : ((Zlength (used_l_2)) = 26)) (PreH31 : ((Zlength (seen_l_2)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)))) = 26)
.

Definition solver_entail_wit_7_1_split_goal_3 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) >= 0)) (PreH3 : ((Znth last next_l_2 0) < 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l_2)) = 26)) (PreH29 : ((Zlength (prev_l_2)) = 26)) (PreH30 : ((Zlength (used_l_2)) = 26)) (PreH31 : ((Zlength (seen_l_2)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)))) = 26)
.

Definition solver_entail_wit_7_1_split_goal_4 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) >= 0)) (PreH3 : ((Znth last next_l_2 0) < 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l_2)) = 26)) (PreH29 : ((Zlength (prev_l_2)) = 26)) (PreH30 : ((Zlength (used_l_2)) = 26)) (PreH31 : ((Zlength (seen_l_2)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l_2)))) = 26)
.

Definition solver_entail_wit_7_1_split_goal_5 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) >= 0)) (PreH3 : ((Znth last next_l_2 0) < 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l_2)) = 26)) (PreH29 : ((Zlength (prev_l_2)) = 26)) (PreH30 : ((Zlength (used_l_2)) = 26)) (PreH31 : ((Zlength (seen_l_2)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((Zlength ((replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l_2)))) = 26)
.

Definition solver_entail_wit_7_1_split_goal_6 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) >= 0)) (PreH3 : ((Znth last next_l_2 0) < 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l_2)) = 26)) (PreH29 : ((Zlength (prev_l_2)) = 26)) (PreH30 : ((Zlength (used_l_2)) = 26)) (PreH31 : ((Zlength (seen_l_2)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((i + 1 ) <= (Zlength ((Znth (z) (g) ((@nil Z))))))
.

Definition solver_entail_wit_7_2 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) >= 0)) (PreH3 : ((Znth last next_l_2 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH4 : ((Znth last next_l_2 0) >= 0)) (PreH5 : (last >= 0)) (PreH6 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH7 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH8 : (last <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (z <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (last >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (z >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH17 : (n_pre = (Zlength (g)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (rows)) = n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH22 : (0 <= z)) (PreH23 : (z < n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH26 : ((-1) <= last)) (PreH27 : (last < 26)) (PreH28 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH29 : ((Zlength (next_l_2)) = 26)) (PreH30 : ((Zlength (prev_l_2)) = 26)) (PreH31 : ((Zlength (used_l_2)) = 26)) (PreH32 : ((Zlength (seen_l_2)) = 26)) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH34 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH35 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH36 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH37 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l_2)) )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l_2)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  EX (seen_l: (@list Z))  (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z (i + 1 ) next_l prev_l used_l seen_l ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) ) ”
  &&  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) >= 0)) (PreH3 : ((Znth last next_l_2 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH4 : ((Znth last next_l_2 0) >= 0)) (PreH5 : (last >= 0)) (PreH6 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH7 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH8 : (last <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (z <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (last >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (z >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH17 : (n_pre = (Zlength (g)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (rows)) = n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH22 : (0 <= z)) (PreH23 : (z < n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH26 : ((-1) <= last)) (PreH27 : (last < 26)) (PreH28 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH29 : ((Zlength (next_l_2)) = 26)) (PreH30 : ((Zlength (prev_l_2)) = 26)) (PreH31 : ((Zlength (used_l_2)) = 26)) (PreH32 : ((Zlength (seen_l_2)) = 26)) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH34 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH35 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH36 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH37 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  TT && emp 
|--
  “ (WordScanState g z (i + 1 ) (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) ) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)))) = 26) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)))) = 26) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l_2)))) = 26) ” 
  &&  “ ((Zlength ((replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l_2)))) = 26) ” 
  &&  “ ((i + 1 ) <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_7_2_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) >= 0)) (PreH3 : ((Znth last next_l_2 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH4 : ((Znth last next_l_2 0) >= 0)) (PreH5 : (last >= 0)) (PreH6 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH7 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH8 : (last <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (z <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (last >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (z >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH17 : (n_pre = (Zlength (g)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (rows)) = n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH22 : (0 <= z)) (PreH23 : (z < n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH26 : ((-1) <= last)) (PreH27 : (last < 26)) (PreH28 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH29 : ((Zlength (next_l_2)) = 26)) (PreH30 : ((Zlength (prev_l_2)) = 26)) (PreH31 : ((Zlength (used_l_2)) = 26)) (PreH32 : ((Zlength (seen_l_2)) = 26)) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH34 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH35 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH36 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH37 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  (WordScanState g z (i + 1 ) (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) )
.

Definition solver_entail_wit_7_2_split_goal_2 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) >= 0)) (PreH3 : ((Znth last next_l_2 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH4 : ((Znth last next_l_2 0) >= 0)) (PreH5 : (last >= 0)) (PreH6 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH7 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH8 : (last <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (z <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (last >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (z >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH17 : (n_pre = (Zlength (g)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (rows)) = n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH22 : (0 <= z)) (PreH23 : (z < n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH26 : ((-1) <= last)) (PreH27 : (last < 26)) (PreH28 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH29 : ((Zlength (next_l_2)) = 26)) (PreH30 : ((Zlength (prev_l_2)) = 26)) (PreH31 : ((Zlength (used_l_2)) = 26)) (PreH32 : ((Zlength (seen_l_2)) = 26)) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH34 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH35 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH36 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH37 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)))) = 26)
.

Definition solver_entail_wit_7_2_split_goal_3 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) >= 0)) (PreH3 : ((Znth last next_l_2 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH4 : ((Znth last next_l_2 0) >= 0)) (PreH5 : (last >= 0)) (PreH6 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH7 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH8 : (last <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (z <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (last >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (z >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH17 : (n_pre = (Zlength (g)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (rows)) = n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH22 : (0 <= z)) (PreH23 : (z < n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH26 : ((-1) <= last)) (PreH27 : (last < 26)) (PreH28 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH29 : ((Zlength (next_l_2)) = 26)) (PreH30 : ((Zlength (prev_l_2)) = 26)) (PreH31 : ((Zlength (used_l_2)) = 26)) (PreH32 : ((Zlength (seen_l_2)) = 26)) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH34 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH35 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH36 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH37 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)))) = 26)
.

Definition solver_entail_wit_7_2_split_goal_4 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) >= 0)) (PreH3 : ((Znth last next_l_2 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH4 : ((Znth last next_l_2 0) >= 0)) (PreH5 : (last >= 0)) (PreH6 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH7 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH8 : (last <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (z <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (last >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (z >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH17 : (n_pre = (Zlength (g)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (rows)) = n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH22 : (0 <= z)) (PreH23 : (z < n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH26 : ((-1) <= last)) (PreH27 : (last < 26)) (PreH28 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH29 : ((Zlength (next_l_2)) = 26)) (PreH30 : ((Zlength (prev_l_2)) = 26)) (PreH31 : ((Zlength (used_l_2)) = 26)) (PreH32 : ((Zlength (seen_l_2)) = 26)) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH34 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH35 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH36 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH37 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l_2)))) = 26)
.

Definition solver_entail_wit_7_2_split_goal_5 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) >= 0)) (PreH3 : ((Znth last next_l_2 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH4 : ((Znth last next_l_2 0) >= 0)) (PreH5 : (last >= 0)) (PreH6 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH7 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH8 : (last <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (z <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (last >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (z >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH17 : (n_pre = (Zlength (g)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (rows)) = n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH22 : (0 <= z)) (PreH23 : (z < n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH26 : ((-1) <= last)) (PreH27 : (last < 26)) (PreH28 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH29 : ((Zlength (next_l_2)) = 26)) (PreH30 : ((Zlength (prev_l_2)) = 26)) (PreH31 : ((Zlength (used_l_2)) = 26)) (PreH32 : ((Zlength (seen_l_2)) = 26)) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH34 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH35 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH36 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH37 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((Zlength ((replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l_2)))) = 26)
.

Definition solver_entail_wit_7_2_split_goal_6 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) >= 0)) (PreH3 : ((Znth last next_l_2 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH4 : ((Znth last next_l_2 0) >= 0)) (PreH5 : (last >= 0)) (PreH6 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH7 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH8 : (last <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (z <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (last >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (z >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH17 : (n_pre = (Zlength (g)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (rows)) = n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH22 : (0 <= z)) (PreH23 : (z < n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH26 : ((-1) <= last)) (PreH27 : (last < 26)) (PreH28 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH29 : ((Zlength (next_l_2)) = 26)) (PreH30 : ((Zlength (prev_l_2)) = 26)) (PreH31 : ((Zlength (used_l_2)) = 26)) (PreH32 : ((Zlength (seen_l_2)) = 26)) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH34 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH35 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH36 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH37 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((i + 1 ) <= (Zlength ((Znth (z) (g) ((@nil Z))))))
.

Definition solver_entail_wit_7_3 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) < 0)) (PreH2 : ((Znth last next_l_2 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : ((Znth last next_l_2 0) >= 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l_2)) = 26)) (PreH29 : ((Zlength (prev_l_2)) = 26)) (PreH30 : ((Zlength (used_l_2)) = 26)) (PreH31 : ((Zlength (seen_l_2)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l_2)) )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l_2)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  EX (seen_l: (@list Z))  (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z (i + 1 ) next_l prev_l used_l seen_l ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) ) ”
  &&  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) < 0)) (PreH2 : ((Znth last next_l_2 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : ((Znth last next_l_2 0) >= 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l_2)) = 26)) (PreH29 : ((Zlength (prev_l_2)) = 26)) (PreH30 : ((Zlength (used_l_2)) = 26)) (PreH31 : ((Zlength (seen_l_2)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  TT && emp 
|--
  “ (WordScanState g z (i + 1 ) (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) ) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)))) = 26) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)))) = 26) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l_2)))) = 26) ” 
  &&  “ ((Zlength ((replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l_2)))) = 26) ” 
  &&  “ ((i + 1 ) <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_7_3_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) < 0)) (PreH2 : ((Znth last next_l_2 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : ((Znth last next_l_2 0) >= 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l_2)) = 26)) (PreH29 : ((Zlength (prev_l_2)) = 26)) (PreH30 : ((Zlength (used_l_2)) = 26)) (PreH31 : ((Zlength (seen_l_2)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  (WordScanState g z (i + 1 ) (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) )
.

Definition solver_entail_wit_7_3_split_goal_2 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) < 0)) (PreH2 : ((Znth last next_l_2 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : ((Znth last next_l_2 0) >= 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l_2)) = 26)) (PreH29 : ((Zlength (prev_l_2)) = 26)) (PreH30 : ((Zlength (used_l_2)) = 26)) (PreH31 : ((Zlength (seen_l_2)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)))) = 26)
.

Definition solver_entail_wit_7_3_split_goal_3 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) < 0)) (PreH2 : ((Znth last next_l_2 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : ((Znth last next_l_2 0) >= 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l_2)) = 26)) (PreH29 : ((Zlength (prev_l_2)) = 26)) (PreH30 : ((Zlength (used_l_2)) = 26)) (PreH31 : ((Zlength (seen_l_2)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)))) = 26)
.

Definition solver_entail_wit_7_3_split_goal_4 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) < 0)) (PreH2 : ((Znth last next_l_2 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : ((Znth last next_l_2 0) >= 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l_2)) = 26)) (PreH29 : ((Zlength (prev_l_2)) = 26)) (PreH30 : ((Zlength (used_l_2)) = 26)) (PreH31 : ((Zlength (seen_l_2)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l_2)))) = 26)
.

Definition solver_entail_wit_7_3_split_goal_5 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) < 0)) (PreH2 : ((Znth last next_l_2 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : ((Znth last next_l_2 0) >= 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l_2)) = 26)) (PreH29 : ((Zlength (prev_l_2)) = 26)) (PreH30 : ((Zlength (used_l_2)) = 26)) (PreH31 : ((Zlength (seen_l_2)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((Zlength ((replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l_2)))) = 26)
.

Definition solver_entail_wit_7_3_split_goal_6 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) < 0)) (PreH2 : ((Znth last next_l_2 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : ((Znth last next_l_2 0) >= 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l_2)) = 26)) (PreH29 : ((Zlength (prev_l_2)) = 26)) (PreH30 : ((Zlength (used_l_2)) = 26)) (PreH31 : ((Zlength (seen_l_2)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((i + 1 ) <= (Zlength ((Znth (z) (g) ((@nil Z))))))
.

Definition solver_entail_wit_7_4 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) < 0)) (PreH2 : ((Znth last next_l_2 0) < 0)) (PreH3 : (last >= 0)) (PreH4 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH6 : (last <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (z <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (last >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (z >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH15 : (n_pre = (Zlength (g)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 100000)) (PreH18 : ((Zlength (rows)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH20 : (0 <= z)) (PreH21 : (z < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH24 : ((-1) <= last)) (PreH25 : (last < 26)) (PreH26 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH27 : ((Zlength (next_l_2)) = 26)) (PreH28 : ((Zlength (prev_l_2)) = 26)) (PreH29 : ((Zlength (used_l_2)) = 26)) (PreH30 : ((Zlength (seen_l_2)) = 26)) (PreH31 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH32 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH33 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH34 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH35 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l_2)) )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l_2)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  EX (seen_l: (@list Z))  (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z (i + 1 ) next_l prev_l used_l seen_l ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) ) ”
  &&  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) < 0)) (PreH2 : ((Znth last next_l_2 0) < 0)) (PreH3 : (last >= 0)) (PreH4 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH6 : (last <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (z <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (last >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (z >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH15 : (n_pre = (Zlength (g)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 100000)) (PreH18 : ((Zlength (rows)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH20 : (0 <= z)) (PreH21 : (z < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH24 : ((-1) <= last)) (PreH25 : (last < 26)) (PreH26 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH27 : ((Zlength (next_l_2)) = 26)) (PreH28 : ((Zlength (prev_l_2)) = 26)) (PreH29 : ((Zlength (used_l_2)) = 26)) (PreH30 : ((Zlength (seen_l_2)) = 26)) (PreH31 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH32 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH33 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH34 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH35 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  TT && emp 
|--
  “ (WordScanState g z (i + 1 ) (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) ) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)))) = 26) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)))) = 26) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l_2)))) = 26) ” 
  &&  “ ((Zlength ((replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l_2)))) = 26) ” 
  &&  “ ((i + 1 ) <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_7_4_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) < 0)) (PreH2 : ((Znth last next_l_2 0) < 0)) (PreH3 : (last >= 0)) (PreH4 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH6 : (last <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (z <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (last >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (z >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH15 : (n_pre = (Zlength (g)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 100000)) (PreH18 : ((Zlength (rows)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH20 : (0 <= z)) (PreH21 : (z < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH24 : ((-1) <= last)) (PreH25 : (last < 26)) (PreH26 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH27 : ((Zlength (next_l_2)) = 26)) (PreH28 : ((Zlength (prev_l_2)) = 26)) (PreH29 : ((Zlength (used_l_2)) = 26)) (PreH30 : ((Zlength (seen_l_2)) = 26)) (PreH31 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH32 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH33 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH34 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH35 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  (WordScanState g z (i + 1 ) (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) )
.

Definition solver_entail_wit_7_4_split_goal_2 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) < 0)) (PreH2 : ((Znth last next_l_2 0) < 0)) (PreH3 : (last >= 0)) (PreH4 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH6 : (last <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (z <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (last >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (z >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH15 : (n_pre = (Zlength (g)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 100000)) (PreH18 : ((Zlength (rows)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH20 : (0 <= z)) (PreH21 : (z < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH24 : ((-1) <= last)) (PreH25 : (last < 26)) (PreH26 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH27 : ((Zlength (next_l_2)) = 26)) (PreH28 : ((Zlength (prev_l_2)) = 26)) (PreH29 : ((Zlength (used_l_2)) = 26)) (PreH30 : ((Zlength (seen_l_2)) = 26)) (PreH31 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH32 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH33 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH34 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH35 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)))) = 26)
.

Definition solver_entail_wit_7_4_split_goal_3 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) < 0)) (PreH2 : ((Znth last next_l_2 0) < 0)) (PreH3 : (last >= 0)) (PreH4 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH6 : (last <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (z <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (last >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (z >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH15 : (n_pre = (Zlength (g)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 100000)) (PreH18 : ((Zlength (rows)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH20 : (0 <= z)) (PreH21 : (z < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH24 : ((-1) <= last)) (PreH25 : (last < 26)) (PreH26 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH27 : ((Zlength (next_l_2)) = 26)) (PreH28 : ((Zlength (prev_l_2)) = 26)) (PreH29 : ((Zlength (used_l_2)) = 26)) (PreH30 : ((Zlength (seen_l_2)) = 26)) (PreH31 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH32 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH33 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH34 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH35 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)))) = 26)
.

Definition solver_entail_wit_7_4_split_goal_4 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) < 0)) (PreH2 : ((Znth last next_l_2 0) < 0)) (PreH3 : (last >= 0)) (PreH4 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH6 : (last <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (z <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (last >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (z >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH15 : (n_pre = (Zlength (g)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 100000)) (PreH18 : ((Zlength (rows)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH20 : (0 <= z)) (PreH21 : (z < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH24 : ((-1) <= last)) (PreH25 : (last < 26)) (PreH26 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH27 : ((Zlength (next_l_2)) = 26)) (PreH28 : ((Zlength (prev_l_2)) = 26)) (PreH29 : ((Zlength (used_l_2)) = 26)) (PreH30 : ((Zlength (seen_l_2)) = 26)) (PreH31 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH32 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH33 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH34 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH35 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (last) (prev_l_2)))) = 26)
.

Definition solver_entail_wit_7_4_split_goal_5 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) < 0)) (PreH2 : ((Znth last next_l_2 0) < 0)) (PreH3 : (last >= 0)) (PreH4 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH6 : (last <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (z <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (last >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (z >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH15 : (n_pre = (Zlength (g)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 100000)) (PreH18 : ((Zlength (rows)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH20 : (0 <= z)) (PreH21 : (z < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH24 : ((-1) <= last)) (PreH25 : (last < 26)) (PreH26 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH27 : ((Zlength (next_l_2)) = 26)) (PreH28 : ((Zlength (prev_l_2)) = 26)) (PreH29 : ((Zlength (used_l_2)) = 26)) (PreH30 : ((Zlength (seen_l_2)) = 26)) (PreH31 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH32 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH33 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH34 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH35 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((Zlength ((replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l_2)))) = 26)
.

Definition solver_entail_wit_7_4_split_goal_6 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l_2 0) < 0)) (PreH2 : ((Znth last next_l_2 0) < 0)) (PreH3 : (last >= 0)) (PreH4 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH6 : (last <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (z <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (last >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (z >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH15 : (n_pre = (Zlength (g)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 100000)) (PreH18 : ((Zlength (rows)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH20 : (0 <= z)) (PreH21 : (z < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH24 : ((-1) <= last)) (PreH25 : (last < 26)) (PreH26 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH27 : ((Zlength (next_l_2)) = 26)) (PreH28 : ((Zlength (prev_l_2)) = 26)) (PreH29 : ((Zlength (used_l_2)) = 26)) (PreH30 : ((Zlength (seen_l_2)) = 26)) (PreH31 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH32 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH33 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH34 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH35 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((i + 1 ) <= (Zlength ((Znth (z) (g) ((@nil Z))))))
.

Definition solver_entail_wit_7_5 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (last < 0)) (PreH2 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH4 : (last <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (z <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (last >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (z >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH13 : (n_pre = (Zlength (g)))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : ((Zlength (rows)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH18 : (0 <= z)) (PreH19 : (z < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH22 : ((-1) <= last)) (PreH23 : (last < 26)) (PreH24 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH25 : ((Zlength (next_l_2)) = 26)) (PreH26 : ((Zlength (prev_l_2)) = 26)) (PreH27 : ((Zlength (used_l_2)) = 26)) (PreH28 : ((Zlength (seen_l_2)) = 26)) (PreH29 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH30 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH31 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH32 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH33 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l_2 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l_2 )
|--
  EX (seen_l: (@list Z))  (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z (i + 1 ) next_l prev_l used_l seen_l ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) ) ”
  &&  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : (last < 0)) (PreH2 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH4 : (last <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (z <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (last >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (z >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH13 : (n_pre = (Zlength (g)))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : ((Zlength (rows)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH18 : (0 <= z)) (PreH19 : (z < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH22 : ((-1) <= last)) (PreH23 : (last < 26)) (PreH24 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH25 : ((Zlength (next_l_2)) = 26)) (PreH26 : ((Zlength (prev_l_2)) = 26)) (PreH27 : ((Zlength (used_l_2)) = 26)) (PreH28 : ((Zlength (seen_l_2)) = 26)) (PreH29 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH30 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH31 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH32 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH33 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  TT && emp 
|--
  “ (WordScanState g z (i + 1 ) next_l_2 prev_l_2 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) ) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)))) = 26) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)))) = 26) ” 
  &&  “ ((i + 1 ) <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_7_5_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : (last < 0)) (PreH2 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH4 : (last <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (z <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (last >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (z >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH13 : (n_pre = (Zlength (g)))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : ((Zlength (rows)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH18 : (0 <= z)) (PreH19 : (z < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH22 : ((-1) <= last)) (PreH23 : (last < 26)) (PreH24 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH25 : ((Zlength (next_l_2)) = 26)) (PreH26 : ((Zlength (prev_l_2)) = 26)) (PreH27 : ((Zlength (used_l_2)) = 26)) (PreH28 : ((Zlength (seen_l_2)) = 26)) (PreH29 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH30 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH31 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH32 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH33 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  (WordScanState g z (i + 1 ) next_l_2 prev_l_2 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)) (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) )
.

Definition solver_entail_wit_7_5_split_goal_2 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : (last < 0)) (PreH2 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH4 : (last <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (z <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (last >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (z >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH13 : (n_pre = (Zlength (g)))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : ((Zlength (rows)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH18 : (0 <= z)) (PreH19 : (z < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH22 : ((-1) <= last)) (PreH23 : (last < 26)) (PreH24 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH25 : ((Zlength (next_l_2)) = 26)) (PreH26 : ((Zlength (prev_l_2)) = 26)) (PreH27 : ((Zlength (used_l_2)) = 26)) (PreH28 : ((Zlength (seen_l_2)) = 26)) (PreH29 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH30 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH31 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH32 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH33 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l_2)))) = 26)
.

Definition solver_entail_wit_7_5_split_goal_3 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : (last < 0)) (PreH2 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH4 : (last <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (z <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (last >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (z >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH13 : (n_pre = (Zlength (g)))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : ((Zlength (rows)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH18 : (0 <= z)) (PreH19 : (z < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH22 : ((-1) <= last)) (PreH23 : (last < 26)) (PreH24 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH25 : ((Zlength (next_l_2)) = 26)) (PreH26 : ((Zlength (prev_l_2)) = 26)) (PreH27 : ((Zlength (used_l_2)) = 26)) (PreH28 : ((Zlength (seen_l_2)) = 26)) (PreH29 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH30 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH31 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH32 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH33 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((Zlength ((replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l_2)))) = 26)
.

Definition solver_entail_wit_7_5_split_goal_4 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (z: Z) (PreH1 : (last < 0)) (PreH2 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH4 : (last <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (z <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (last >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (z >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH13 : (n_pre = (Zlength (g)))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : ((Zlength (rows)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH18 : (0 <= z)) (PreH19 : (z < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH22 : ((-1) <= last)) (PreH23 : (last < 26)) (PreH24 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH25 : ((Zlength (next_l_2)) = 26)) (PreH26 : ((Zlength (prev_l_2)) = 26)) (PreH27 : ((Zlength (used_l_2)) = 26)) (PreH28 : ((Zlength (seen_l_2)) = 26)) (PreH29 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH30 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH31 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH32 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH33 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l_2 0) = 0)) ,
  ((i + 1 ) <= (Zlength ((Znth (z) (g) ((@nil Z))))))
.

Definition solver_entail_wit_8 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : (0 <= z)) (PreH7 : (z < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH10 : ((-1) <= last)) (PreH11 : (last < 26)) (PreH12 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH13 : ((Zlength (next_l_2)) = 26)) (PreH14 : ((Zlength (prev_l_2)) = 26)) (PreH15 : ((Zlength (used_l_2)) = 26)) (PreH16 : ((Zlength (seen_l_2)) = 26)) (PreH17 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH19 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH20 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) = 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l_2 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l_2 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l_2 )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l_2 )
|--
  EX (seen_l: (@list Z))  (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g (z + 1 ) next_l prev_l used_l ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
) \/
(
forall (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH11 : ((-1) <= last)) (PreH12 : (last < 26)) (PreH13 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH14 : ((Zlength (next_l_2)) = 26)) (PreH15 : ((Zlength (prev_l_2)) = 26)) (PreH16 : ((Zlength (used_l_2)) = 26)) (PreH17 : ((Zlength (seen_l_2)) = 26)) (PreH18 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH19 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH20 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH21 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) = 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
|--
  “ (GraphBuildState g (z + 1 ) next_l_2 prev_l_2 used_l_2 ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26))) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
).

Definition solver_entail_wit_8_split_goal_1 := 
forall (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH11 : ((-1) <= last)) (PreH12 : (last < 26)) (PreH13 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH14 : ((Zlength (next_l_2)) = 26)) (PreH15 : ((Zlength (prev_l_2)) = 26)) (PreH16 : ((Zlength (used_l_2)) = 26)) (PreH17 : ((Zlength (seen_l_2)) = 26)) (PreH18 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH19 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH20 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH21 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) = 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
|--
  “ (GraphBuildState g (z + 1 ) next_l_2 prev_l_2 used_l_2 ) ”
.

Definition solver_entail_wit_8_split_goal_2 := 
forall (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH11 : ((-1) <= last)) (PreH12 : (last < 26)) (PreH13 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH14 : ((Zlength (next_l_2)) = 26)) (PreH15 : ((Zlength (prev_l_2)) = 26)) (PreH16 : ((Zlength (used_l_2)) = 26)) (PreH17 : ((Zlength (seen_l_2)) = 26)) (PreH18 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH19 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH20 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH21 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) = 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
|--
  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26))) ”
.

Definition solver_entail_wit_8_split_goal_3 := 
forall (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH11 : ((-1) <= last)) (PreH12 : (last < 26)) (PreH13 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH14 : ((Zlength (next_l_2)) = 26)) (PreH15 : ((Zlength (prev_l_2)) = 26)) (PreH16 : ((Zlength (used_l_2)) = 26)) (PreH17 : ((Zlength (seen_l_2)) = 26)) (PreH18 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH19 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH20 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH21 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) = 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
|--
  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26))) ”
.

Definition solver_entail_wit_8_split_goal_4 := 
forall (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH11 : ((-1) <= last)) (PreH12 : (last < 26)) (PreH13 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH14 : ((Zlength (next_l_2)) = 26)) (PreH15 : ((Zlength (prev_l_2)) = 26)) (PreH16 : ((Zlength (used_l_2)) = 26)) (PreH17 : ((Zlength (seen_l_2)) = 26)) (PreH18 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH19 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH20 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH21 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) = 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
|--
  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ”
.

Definition solver_entail_wit_8_split_goal_5 := 
forall (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH11 : ((-1) <= last)) (PreH12 : (last < 26)) (PreH13 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH14 : ((Zlength (next_l_2)) = 26)) (PreH15 : ((Zlength (prev_l_2)) = 26)) (PreH16 : ((Zlength (used_l_2)) = 26)) (PreH17 : ((Zlength (seen_l_2)) = 26)) (PreH18 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH19 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH20 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH21 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) = 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ”
.

Definition solver_entail_wit_8_split_goal_spatial := 
forall (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH11 : ((-1) <= last)) (PreH12 : (last < 26)) (PreH13 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH14 : ((Zlength (next_l_2)) = 26)) (PreH15 : ((Zlength (prev_l_2)) = 26)) (PreH16 : ((Zlength (used_l_2)) = 26)) (PreH17 : ((Zlength (seen_l_2)) = 26)) (PreH18 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH19 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH20 : (WordScanState g z i next_l_2 prev_l_2 used_l_2 seen_l_2 last )) (PreH21 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) = 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
|--
  (CharPtrArray2.full words_pre n_pre rows )
.

Definition solver_entail_wit_9 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l_2: (@list Z)) (prev_l_2: (@list Z)) (used_l_2: (@list Z)) (seen_l: (@list Z)) (z: Z) (last: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : ((-1) <= last)) (PreH10 : (last < 26)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : ((Zlength (seen_l)) = 26)) (PreH15 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH16 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH17 : (GraphBuildState g (z + 1 ) next_l_2 prev_l_2 used_l_2 )) ,
  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l_2 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l_2 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l_2 )
|--
  EX (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ (0 <= (z + 1 )) ” 
  &&  “ ((z + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g (z + 1 ) next_l prev_l used_l ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l_2: (@list Z)) (prev_l_2: (@list Z)) (used_l_2: (@list Z)) (seen_l: (@list Z)) (z: Z) (last: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : ((-1) <= last)) (PreH10 : (last < 26)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : ((Zlength (seen_l)) = 26)) (PreH15 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH16 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH17 : (GraphBuildState g (z + 1 ) next_l_2 prev_l_2 used_l_2 )) ,
  TT && emp 
|--
  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26))) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ”
  &&  emp
).

Definition solver_entail_wit_9_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l_2: (@list Z)) (prev_l_2: (@list Z)) (used_l_2: (@list Z)) (seen_l: (@list Z)) (z: Z) (last: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : ((-1) <= last)) (PreH10 : (last < 26)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : ((Zlength (seen_l)) = 26)) (PreH15 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH16 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH17 : (GraphBuildState g (z + 1 ) next_l_2 prev_l_2 used_l_2 )) ,
  forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))
.

Definition solver_entail_wit_9_split_goal_2 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l_2: (@list Z)) (prev_l_2: (@list Z)) (used_l_2: (@list Z)) (seen_l: (@list Z)) (z: Z) (last: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : ((-1) <= last)) (PreH10 : (last < 26)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : ((Zlength (seen_l)) = 26)) (PreH15 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH16 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH17 : (GraphBuildState g (z + 1 ) next_l_2 prev_l_2 used_l_2 )) ,
  forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))
.

Definition solver_entail_wit_9_split_goal_3 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l_2: (@list Z)) (prev_l_2: (@list Z)) (used_l_2: (@list Z)) (seen_l: (@list Z)) (z: Z) (last: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : ((-1) <= last)) (PreH10 : (last < 26)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : ((Zlength (seen_l)) = 26)) (PreH15 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH16 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH17 : (GraphBuildState g (z + 1 ) next_l_2 prev_l_2 used_l_2 )) ,
  forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))
.

Definition solver_entail_wit_9_split_goal_4 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l_2: (@list Z)) (prev_l_2: (@list Z)) (used_l_2: (@list Z)) (seen_l: (@list Z)) (z: Z) (last: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> (((((0 < (Zlength ((Znth (k_5) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_5) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_5) (rows) ((@nil Z))) = (c_string ((Znth (k_5) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_5) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_5) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : forall (k_6: Z) , forall (q_2: Z) , (((((0 <= k_6) /\ (k_6 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_6) (g) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_6) (g) ((@nil Z)))) (0)) <= 122)))) (PreH7 : (0 <= z)) (PreH8 : (z < n_pre)) (PreH9 : ((-1) <= last)) (PreH10 : (last < 26)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : ((Zlength (seen_l)) = 26)) (PreH15 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < 26)) -> (((-1) <= (Znth (k_7) (next_l_2) ((-1)))) /\ ((Znth (k_7) (next_l_2) ((-1))) < 26)))) (PreH16 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < 26)) -> (((-1) <= (Znth (k_8) (prev_l_2) ((-1)))) /\ ((Znth (k_8) (prev_l_2) ((-1))) < 26)))) (PreH17 : (GraphBuildState g (z + 1 ) next_l_2 prev_l_2 used_l_2 )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))
.

Definition solver_entail_wit_10 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (z: Z) (PreH1 : (z >= n_pre)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> (((((0 < (Zlength ((Znth (k_3) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_3) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_3) (rows) ((@nil Z))) = (c_string ((Znth (k_3) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_3) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_3) (g) ((@nil Z))))) < INT_MAX)))) (PreH7 : forall (k_4: Z) , forall (q: Z) , (((((0 <= k_4) /\ (k_4 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_4) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_4) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_4) (g) ((@nil Z)))) (0)) <= 122)))) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (next_l_2)) = 26)) (PreH11 : ((Zlength (prev_l_2)) = 26)) (PreH12 : ((Zlength (used_l_2)) = 26)) (PreH13 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < 26)) -> (((-1) <= (Znth (k_5) (next_l_2) ((-1)))) /\ ((Znth (k_5) (next_l_2) ((-1))) < 26)))) (PreH14 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < 26)) -> (((-1) <= (Znth (k_6) (prev_l_2) ((-1)))) /\ ((Znth (k_6) (prev_l_2) ((-1))) < 26)))) (PreH15 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  (IntArray.full ( &( "visited" ) ) 26 (repeat_Z (0) (26)) )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l_2 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l_2 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l_2 )
|--
  EX (visited_l: (@list Z))  (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z))  (output_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 26) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 26) ” 
  &&  “ ((Zlength (output_l)) = 0) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (visited_l)) = 26) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g n_pre next_l prev_l used_l ) ” 
  &&  “ (TraversalState next_l prev_l used_l 0 visited_l output_l ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 0 output_l )
  **  (CharArray.undef_seg out_pre 0 64 )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (z: Z) (PreH1 : (z >= n_pre)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> (((((0 < (Zlength ((Znth (k_3) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_3) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_3) (rows) ((@nil Z))) = (c_string ((Znth (k_3) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_3) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_3) (g) ((@nil Z))))) < INT_MAX)))) (PreH7 : forall (k_4: Z) , forall (q: Z) , (((((0 <= k_4) /\ (k_4 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_4) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_4) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_4) (g) ((@nil Z)))) (0)) <= 122)))) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (next_l_2)) = 26)) (PreH11 : ((Zlength (prev_l_2)) = 26)) (PreH12 : ((Zlength (used_l_2)) = 26)) (PreH13 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < 26)) -> (((-1) <= (Znth (k_5) (next_l_2) ((-1)))) /\ ((Znth (k_5) (next_l_2) ((-1))) < 26)))) (PreH14 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < 26)) -> (((-1) <= (Znth (k_6) (prev_l_2) ((-1)))) /\ ((Znth (k_6) (prev_l_2) ((-1))) < 26)))) (PreH15 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  TT && emp 
|--
  “ (TraversalState next_l_2 prev_l_2 used_l_2 0 (repeat_Z (0) (26)) (@nil Z) ) ” 
  &&  “ (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26))) ” 
  &&  “ ((Zlength ((repeat_Z (0) (26)))) = 26) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition solver_entail_wit_10_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (z: Z) (PreH1 : (z >= n_pre)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> (((((0 < (Zlength ((Znth (k_3) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_3) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_3) (rows) ((@nil Z))) = (c_string ((Znth (k_3) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_3) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_3) (g) ((@nil Z))))) < INT_MAX)))) (PreH7 : forall (k_4: Z) , forall (q: Z) , (((((0 <= k_4) /\ (k_4 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_4) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_4) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_4) (g) ((@nil Z)))) (0)) <= 122)))) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (next_l_2)) = 26)) (PreH11 : ((Zlength (prev_l_2)) = 26)) (PreH12 : ((Zlength (used_l_2)) = 26)) (PreH13 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < 26)) -> (((-1) <= (Znth (k_5) (next_l_2) ((-1)))) /\ ((Znth (k_5) (next_l_2) ((-1))) < 26)))) (PreH14 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < 26)) -> (((-1) <= (Znth (k_6) (prev_l_2) ((-1)))) /\ ((Znth (k_6) (prev_l_2) ((-1))) < 26)))) (PreH15 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  (TraversalState next_l_2 prev_l_2 used_l_2 0 (repeat_Z (0) (26)) (@nil Z) )
.

Definition solver_entail_wit_10_split_goal_2 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (z: Z) (PreH1 : (z >= n_pre)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> (((((0 < (Zlength ((Znth (k_3) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_3) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_3) (rows) ((@nil Z))) = (c_string ((Znth (k_3) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_3) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_3) (g) ((@nil Z))))) < INT_MAX)))) (PreH7 : forall (k_4: Z) , forall (q: Z) , (((((0 <= k_4) /\ (k_4 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_4) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_4) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_4) (g) ((@nil Z)))) (0)) <= 122)))) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (next_l_2)) = 26)) (PreH11 : ((Zlength (prev_l_2)) = 26)) (PreH12 : ((Zlength (used_l_2)) = 26)) (PreH13 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < 26)) -> (((-1) <= (Znth (k_5) (next_l_2) ((-1)))) /\ ((Znth (k_5) (next_l_2) ((-1))) < 26)))) (PreH14 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < 26)) -> (((-1) <= (Znth (k_6) (prev_l_2) ((-1)))) /\ ((Znth (k_6) (prev_l_2) ((-1))) < 26)))) (PreH15 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )
.

Definition solver_entail_wit_10_split_goal_3 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (z: Z) (PreH1 : (z >= n_pre)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> (((((0 < (Zlength ((Znth (k_3) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_3) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_3) (rows) ((@nil Z))) = (c_string ((Znth (k_3) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_3) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_3) (g) ((@nil Z))))) < INT_MAX)))) (PreH7 : forall (k_4: Z) , forall (q: Z) , (((((0 <= k_4) /\ (k_4 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_4) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_4) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_4) (g) ((@nil Z)))) (0)) <= 122)))) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (next_l_2)) = 26)) (PreH11 : ((Zlength (prev_l_2)) = 26)) (PreH12 : ((Zlength (used_l_2)) = 26)) (PreH13 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < 26)) -> (((-1) <= (Znth (k_5) (next_l_2) ((-1)))) /\ ((Znth (k_5) (next_l_2) ((-1))) < 26)))) (PreH14 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < 26)) -> (((-1) <= (Znth (k_6) (prev_l_2) ((-1)))) /\ ((Znth (k_6) (prev_l_2) ((-1))) < 26)))) (PreH15 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))
.

Definition solver_entail_wit_10_split_goal_4 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (z: Z) (PreH1 : (z >= n_pre)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> (((((0 < (Zlength ((Znth (k_3) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_3) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_3) (rows) ((@nil Z))) = (c_string ((Znth (k_3) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_3) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_3) (g) ((@nil Z))))) < INT_MAX)))) (PreH7 : forall (k_4: Z) , forall (q: Z) , (((((0 <= k_4) /\ (k_4 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_4) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_4) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_4) (g) ((@nil Z)))) (0)) <= 122)))) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (next_l_2)) = 26)) (PreH11 : ((Zlength (prev_l_2)) = 26)) (PreH12 : ((Zlength (used_l_2)) = 26)) (PreH13 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < 26)) -> (((-1) <= (Znth (k_5) (next_l_2) ((-1)))) /\ ((Znth (k_5) (next_l_2) ((-1))) < 26)))) (PreH14 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < 26)) -> (((-1) <= (Znth (k_6) (prev_l_2) ((-1)))) /\ ((Znth (k_6) (prev_l_2) ((-1))) < 26)))) (PreH15 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))
.

Definition solver_entail_wit_10_split_goal_5 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (z: Z) (PreH1 : (z >= n_pre)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> (((((0 < (Zlength ((Znth (k_3) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_3) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_3) (rows) ((@nil Z))) = (c_string ((Znth (k_3) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_3) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_3) (g) ((@nil Z))))) < INT_MAX)))) (PreH7 : forall (k_4: Z) , forall (q: Z) , (((((0 <= k_4) /\ (k_4 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_4) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_4) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_4) (g) ((@nil Z)))) (0)) <= 122)))) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (next_l_2)) = 26)) (PreH11 : ((Zlength (prev_l_2)) = 26)) (PreH12 : ((Zlength (used_l_2)) = 26)) (PreH13 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < 26)) -> (((-1) <= (Znth (k_5) (next_l_2) ((-1)))) /\ ((Znth (k_5) (next_l_2) ((-1))) < 26)))) (PreH14 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < 26)) -> (((-1) <= (Znth (k_6) (prev_l_2) ((-1)))) /\ ((Znth (k_6) (prev_l_2) ((-1))) < 26)))) (PreH15 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  ((Zlength ((repeat_Z (0) (26)))) = 26)
.

Definition solver_entail_wit_10_split_goal_6 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (z: Z) (PreH1 : (z >= n_pre)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> (((((0 < (Zlength ((Znth (k_3) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k_3) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k_3) (rows) ((@nil Z))) = (c_string ((Znth (k_3) (g) ((@nil Z))))))) /\ (valid_string (Znth (k_3) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k_3) (g) ((@nil Z))))) < INT_MAX)))) (PreH7 : forall (k_4: Z) , forall (q: Z) , (((((0 <= k_4) /\ (k_4 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_4) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_4) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_4) (g) ((@nil Z)))) (0)) <= 122)))) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (next_l_2)) = 26)) (PreH11 : ((Zlength (prev_l_2)) = 26)) (PreH12 : ((Zlength (used_l_2)) = 26)) (PreH13 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < 26)) -> (((-1) <= (Znth (k_5) (next_l_2) ((-1)))) /\ ((Znth (k_5) (next_l_2) ((-1))) < 26)))) (PreH14 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < 26)) -> (((-1) <= (Znth (k_6) (prev_l_2) ((-1)))) /\ ((Znth (k_6) (prev_l_2) ((-1))) < 26)))) (PreH15 : (GraphBuildState g z next_l_2 prev_l_2 used_l_2 )) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition solver_entail_wit_11 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (start: Z) (PreH1 : ((Znth start prev_l_2 0) < 0)) (PreH2 : ((Znth start used_l_2 0) <> 0)) (PreH3 : (start < 26)) (PreH4 : (n_pre = (Zlength (g)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= start)) (PreH9 : (start <= 26)) (PreH10 : (0 <= len)) (PreH11 : (len <= 26)) (PreH12 : ((Zlength (output_l_2)) = len)) (PreH13 : ((Zlength (next_l_2)) = 26)) (PreH14 : ((Zlength (prev_l_2)) = 26)) (PreH15 : ((Zlength (used_l_2)) = 26)) (PreH16 : ((Zlength (visited_l_2)) = 26)) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH19 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH20 : (TraversalState next_l_2 prev_l_2 used_l_2 start visited_l_2 output_l_2 )) ,
  (IntArray.full ( &( "prev" ) ) 26 prev_l_2 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l_2 )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l_2 )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l_2 )
  **  (CharArray.seg out_pre 0 len output_l_2 )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  EX (visited_l: (@list Z))  (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z))  (output_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < 26) ” 
  &&  “ ((-1) <= start) ” 
  &&  “ (start < 26) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 26) ” 
  &&  “ ((Zlength (output_l)) = len) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (visited_l)) = 26) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g n_pre next_l prev_l used_l ) ” 
  &&  “ (PathScanState next_l prev_l used_l start start visited_l output_l ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (start: Z) (PreH1 : ((Znth start prev_l_2 0) < 0)) (PreH2 : ((Znth start used_l_2 0) <> 0)) (PreH3 : (start < 26)) (PreH4 : (n_pre = (Zlength (g)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= start)) (PreH9 : (start <= 26)) (PreH10 : (0 <= len)) (PreH11 : (len <= 26)) (PreH12 : ((Zlength (output_l_2)) = len)) (PreH13 : ((Zlength (next_l_2)) = 26)) (PreH14 : ((Zlength (prev_l_2)) = 26)) (PreH15 : ((Zlength (used_l_2)) = 26)) (PreH16 : ((Zlength (visited_l_2)) = 26)) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH19 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH20 : (TraversalState next_l_2 prev_l_2 used_l_2 start visited_l_2 output_l_2 )) ,
  TT && emp 
|--
  “ (PathScanState next_l_2 prev_l_2 used_l_2 start start visited_l_2 output_l_2 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26))) ”
  &&  emp
).

Definition solver_entail_wit_11_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (start: Z) (PreH1 : ((Znth start prev_l_2 0) < 0)) (PreH2 : ((Znth start used_l_2 0) <> 0)) (PreH3 : (start < 26)) (PreH4 : (n_pre = (Zlength (g)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= start)) (PreH9 : (start <= 26)) (PreH10 : (0 <= len)) (PreH11 : (len <= 26)) (PreH12 : ((Zlength (output_l_2)) = len)) (PreH13 : ((Zlength (next_l_2)) = 26)) (PreH14 : ((Zlength (prev_l_2)) = 26)) (PreH15 : ((Zlength (used_l_2)) = 26)) (PreH16 : ((Zlength (visited_l_2)) = 26)) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH19 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH20 : (TraversalState next_l_2 prev_l_2 used_l_2 start visited_l_2 output_l_2 )) ,
  (PathScanState next_l_2 prev_l_2 used_l_2 start start visited_l_2 output_l_2 )
.

Definition solver_entail_wit_11_split_goal_2 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (start: Z) (PreH1 : ((Znth start prev_l_2 0) < 0)) (PreH2 : ((Znth start used_l_2 0) <> 0)) (PreH3 : (start < 26)) (PreH4 : (n_pre = (Zlength (g)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= start)) (PreH9 : (start <= 26)) (PreH10 : (0 <= len)) (PreH11 : (len <= 26)) (PreH12 : ((Zlength (output_l_2)) = len)) (PreH13 : ((Zlength (next_l_2)) = 26)) (PreH14 : ((Zlength (prev_l_2)) = 26)) (PreH15 : ((Zlength (used_l_2)) = 26)) (PreH16 : ((Zlength (visited_l_2)) = 26)) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH19 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH20 : (TraversalState next_l_2 prev_l_2 used_l_2 start visited_l_2 output_l_2 )) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))
.

Definition solver_entail_wit_11_split_goal_3 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (start: Z) (PreH1 : ((Znth start prev_l_2 0) < 0)) (PreH2 : ((Znth start used_l_2 0) <> 0)) (PreH3 : (start < 26)) (PreH4 : (n_pre = (Zlength (g)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= start)) (PreH9 : (start <= 26)) (PreH10 : (0 <= len)) (PreH11 : (len <= 26)) (PreH12 : ((Zlength (output_l_2)) = len)) (PreH13 : ((Zlength (next_l_2)) = 26)) (PreH14 : ((Zlength (prev_l_2)) = 26)) (PreH15 : ((Zlength (used_l_2)) = 26)) (PreH16 : ((Zlength (visited_l_2)) = 26)) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH19 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH20 : (TraversalState next_l_2 prev_l_2 used_l_2 start visited_l_2 output_l_2 )) ,
  forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))
.

Definition solver_entail_wit_12 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : ((Znth c visited_l_2 0) = 0)) (PreH2 : (c >= 0)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start < 26)) (PreH9 : ((-1) <= c)) (PreH10 : (c < 26)) (PreH11 : (0 <= len)) (PreH12 : (len <= 26)) (PreH13 : ((Zlength (output_l_2)) = len)) (PreH14 : ((Zlength (next_l_2)) = 26)) (PreH15 : ((Zlength (prev_l_2)) = 26)) (PreH16 : ((Zlength (used_l_2)) = 26)) (PreH17 : ((Zlength (visited_l_2)) = 26)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH20 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH21 : (PathScanState next_l_2 prev_l_2 used_l_2 start c visited_l_2 output_l_2 )) ,
  (IntArray.full ( &( "next" ) ) 26 next_l_2 )
  **  (CharArray.seg out_pre 0 (len + 1 ) (app (output_l_2) ((cons ((97 + c )) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (len + 1 ) 64 )
  **  (IntArray.full ( &( "visited" ) ) 26 (replace_Znth (c) (1) (visited_l_2)) )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l_2 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l_2 )
|--
  EX (visited_l: (@list Z))  (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z))  (output_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < 26) ” 
  &&  “ ((-1) <= (Znth c next_l_2 0)) ” 
  &&  “ ((Znth c next_l_2 0) < 26) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ ((len + 1 ) <= 26) ” 
  &&  “ ((Zlength (output_l)) = (len + 1 )) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (visited_l)) = 26) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g n_pre next_l prev_l used_l ) ” 
  &&  “ (PathScanState next_l prev_l used_l start (Znth c next_l_2 0) visited_l output_l ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 (len + 1 ) output_l )
  **  (CharArray.undef_seg out_pre (len + 1 ) 64 )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : ((Znth c visited_l_2 0) = 0)) (PreH2 : (c >= 0)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start < 26)) (PreH9 : ((-1) <= c)) (PreH10 : (c < 26)) (PreH11 : (0 <= len)) (PreH12 : (len <= 26)) (PreH13 : ((Zlength (output_l_2)) = len)) (PreH14 : ((Zlength (next_l_2)) = 26)) (PreH15 : ((Zlength (prev_l_2)) = 26)) (PreH16 : ((Zlength (used_l_2)) = 26)) (PreH17 : ((Zlength (visited_l_2)) = 26)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH20 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH21 : (PathScanState next_l_2 prev_l_2 used_l_2 start c visited_l_2 output_l_2 )) ,
  TT && emp 
|--
  “ (PathScanState next_l_2 prev_l_2 used_l_2 start (Znth c next_l_2 0) (replace_Znth (c) (1) (visited_l_2)) (app (output_l_2) ((cons ((97 + c )) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((replace_Znth (c) (1) (visited_l_2)))) = 26) ” 
  &&  “ ((Zlength ((app (output_l_2) ((cons ((97 + c )) ((@nil Z))))))) = (len + 1 )) ” 
  &&  “ ((len + 1 ) <= 26) ” 
  &&  “ ((Znth c next_l_2 0) < 26) ” 
  &&  “ ((-1) <= (Znth c next_l_2 0)) ”
  &&  emp
).

Definition solver_entail_wit_12_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : ((Znth c visited_l_2 0) = 0)) (PreH2 : (c >= 0)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start < 26)) (PreH9 : ((-1) <= c)) (PreH10 : (c < 26)) (PreH11 : (0 <= len)) (PreH12 : (len <= 26)) (PreH13 : ((Zlength (output_l_2)) = len)) (PreH14 : ((Zlength (next_l_2)) = 26)) (PreH15 : ((Zlength (prev_l_2)) = 26)) (PreH16 : ((Zlength (used_l_2)) = 26)) (PreH17 : ((Zlength (visited_l_2)) = 26)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH20 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH21 : (PathScanState next_l_2 prev_l_2 used_l_2 start c visited_l_2 output_l_2 )) ,
  (PathScanState next_l_2 prev_l_2 used_l_2 start (Znth c next_l_2 0) (replace_Znth (c) (1) (visited_l_2)) (app (output_l_2) ((cons ((97 + c )) ((@nil Z))))) )
.

Definition solver_entail_wit_12_split_goal_2 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : ((Znth c visited_l_2 0) = 0)) (PreH2 : (c >= 0)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start < 26)) (PreH9 : ((-1) <= c)) (PreH10 : (c < 26)) (PreH11 : (0 <= len)) (PreH12 : (len <= 26)) (PreH13 : ((Zlength (output_l_2)) = len)) (PreH14 : ((Zlength (next_l_2)) = 26)) (PreH15 : ((Zlength (prev_l_2)) = 26)) (PreH16 : ((Zlength (used_l_2)) = 26)) (PreH17 : ((Zlength (visited_l_2)) = 26)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH20 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH21 : (PathScanState next_l_2 prev_l_2 used_l_2 start c visited_l_2 output_l_2 )) ,
  ((Zlength ((replace_Znth (c) (1) (visited_l_2)))) = 26)
.

Definition solver_entail_wit_12_split_goal_3 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : ((Znth c visited_l_2 0) = 0)) (PreH2 : (c >= 0)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start < 26)) (PreH9 : ((-1) <= c)) (PreH10 : (c < 26)) (PreH11 : (0 <= len)) (PreH12 : (len <= 26)) (PreH13 : ((Zlength (output_l_2)) = len)) (PreH14 : ((Zlength (next_l_2)) = 26)) (PreH15 : ((Zlength (prev_l_2)) = 26)) (PreH16 : ((Zlength (used_l_2)) = 26)) (PreH17 : ((Zlength (visited_l_2)) = 26)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH20 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH21 : (PathScanState next_l_2 prev_l_2 used_l_2 start c visited_l_2 output_l_2 )) ,
  ((Zlength ((app (output_l_2) ((cons ((97 + c )) ((@nil Z))))))) = (len + 1 ))
.

Definition solver_entail_wit_12_split_goal_4 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : ((Znth c visited_l_2 0) = 0)) (PreH2 : (c >= 0)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start < 26)) (PreH9 : ((-1) <= c)) (PreH10 : (c < 26)) (PreH11 : (0 <= len)) (PreH12 : (len <= 26)) (PreH13 : ((Zlength (output_l_2)) = len)) (PreH14 : ((Zlength (next_l_2)) = 26)) (PreH15 : ((Zlength (prev_l_2)) = 26)) (PreH16 : ((Zlength (used_l_2)) = 26)) (PreH17 : ((Zlength (visited_l_2)) = 26)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH20 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH21 : (PathScanState next_l_2 prev_l_2 used_l_2 start c visited_l_2 output_l_2 )) ,
  ((len + 1 ) <= 26)
.

Definition solver_entail_wit_12_split_goal_5 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : ((Znth c visited_l_2 0) = 0)) (PreH2 : (c >= 0)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start < 26)) (PreH9 : ((-1) <= c)) (PreH10 : (c < 26)) (PreH11 : (0 <= len)) (PreH12 : (len <= 26)) (PreH13 : ((Zlength (output_l_2)) = len)) (PreH14 : ((Zlength (next_l_2)) = 26)) (PreH15 : ((Zlength (prev_l_2)) = 26)) (PreH16 : ((Zlength (used_l_2)) = 26)) (PreH17 : ((Zlength (visited_l_2)) = 26)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH20 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH21 : (PathScanState next_l_2 prev_l_2 used_l_2 start c visited_l_2 output_l_2 )) ,
  ((Znth c next_l_2 0) < 26)
.

Definition solver_entail_wit_12_split_goal_6 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : ((Znth c visited_l_2 0) = 0)) (PreH2 : (c >= 0)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start < 26)) (PreH9 : ((-1) <= c)) (PreH10 : (c < 26)) (PreH11 : (0 <= len)) (PreH12 : (len <= 26)) (PreH13 : ((Zlength (output_l_2)) = len)) (PreH14 : ((Zlength (next_l_2)) = 26)) (PreH15 : ((Zlength (prev_l_2)) = 26)) (PreH16 : ((Zlength (used_l_2)) = 26)) (PreH17 : ((Zlength (visited_l_2)) = 26)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH20 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH21 : (PathScanState next_l_2 prev_l_2 used_l_2 start c visited_l_2 output_l_2 )) ,
  ((-1) <= (Znth c next_l_2 0))
.

Definition solver_entail_wit_13_1 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : (c < 0)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= start)) (PreH7 : (start < 26)) (PreH8 : ((-1) <= c)) (PreH9 : (c < 26)) (PreH10 : (0 <= len)) (PreH11 : (len <= 26)) (PreH12 : ((Zlength (output_l_2)) = len)) (PreH13 : ((Zlength (next_l_2)) = 26)) (PreH14 : ((Zlength (prev_l_2)) = 26)) (PreH15 : ((Zlength (used_l_2)) = 26)) (PreH16 : ((Zlength (visited_l_2)) = 26)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH19 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH20 : (PathScanState next_l_2 prev_l_2 used_l_2 start c visited_l_2 output_l_2 )) ,
  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l_2 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l_2 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l_2 )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l_2 )
  **  (CharArray.seg out_pre 0 len output_l_2 )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  EX (visited_l: (@list Z))  (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z))  (output_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < 26) ” 
  &&  “ ((-1) <= c) ” 
  &&  “ (c < 26) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 26) ” 
  &&  “ ((Zlength (output_l)) = len) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (visited_l)) = 26) ” 
  &&  “ (GraphBuildState g n_pre next_l prev_l used_l ) ” 
  &&  “ (TraversalState next_l prev_l used_l (start + 1 ) visited_l output_l ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : (c < 0)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= start)) (PreH7 : (start < 26)) (PreH8 : ((-1) <= c)) (PreH9 : (c < 26)) (PreH10 : (0 <= len)) (PreH11 : (len <= 26)) (PreH12 : ((Zlength (output_l_2)) = len)) (PreH13 : ((Zlength (next_l_2)) = 26)) (PreH14 : ((Zlength (prev_l_2)) = 26)) (PreH15 : ((Zlength (used_l_2)) = 26)) (PreH16 : ((Zlength (visited_l_2)) = 26)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH19 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH20 : (PathScanState next_l_2 prev_l_2 used_l_2 start c visited_l_2 output_l_2 )) ,
  TT && emp 
|--
  “ (TraversalState next_l_2 prev_l_2 used_l_2 (start + 1 ) visited_l_2 output_l_2 ) ”
  &&  emp
).

Definition solver_entail_wit_13_1_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : (c < 0)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= start)) (PreH7 : (start < 26)) (PreH8 : ((-1) <= c)) (PreH9 : (c < 26)) (PreH10 : (0 <= len)) (PreH11 : (len <= 26)) (PreH12 : ((Zlength (output_l_2)) = len)) (PreH13 : ((Zlength (next_l_2)) = 26)) (PreH14 : ((Zlength (prev_l_2)) = 26)) (PreH15 : ((Zlength (used_l_2)) = 26)) (PreH16 : ((Zlength (visited_l_2)) = 26)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH19 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH20 : (PathScanState next_l_2 prev_l_2 used_l_2 start c visited_l_2 output_l_2 )) ,
  (TraversalState next_l_2 prev_l_2 used_l_2 (start + 1 ) visited_l_2 output_l_2 )
.

Definition solver_entail_wit_13_2 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : ((Znth c visited_l_2 0) <> 0)) (PreH2 : (c >= 0)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start < 26)) (PreH9 : ((-1) <= c)) (PreH10 : (c < 26)) (PreH11 : (0 <= len)) (PreH12 : (len <= 26)) (PreH13 : ((Zlength (output_l_2)) = len)) (PreH14 : ((Zlength (next_l_2)) = 26)) (PreH15 : ((Zlength (prev_l_2)) = 26)) (PreH16 : ((Zlength (used_l_2)) = 26)) (PreH17 : ((Zlength (visited_l_2)) = 26)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH20 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH21 : (PathScanState next_l_2 prev_l_2 used_l_2 start c visited_l_2 output_l_2 )) ,
  (IntArray.full ( &( "visited" ) ) 26 visited_l_2 )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l_2 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l_2 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l_2 )
  **  (CharArray.seg out_pre 0 len output_l_2 )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  EX (visited_l: (@list Z))  (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z))  (output_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < 26) ” 
  &&  “ ((-1) <= c) ” 
  &&  “ (c < 26) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 26) ” 
  &&  “ ((Zlength (output_l)) = len) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (visited_l)) = 26) ” 
  &&  “ (GraphBuildState g n_pre next_l prev_l used_l ) ” 
  &&  “ (TraversalState next_l prev_l used_l (start + 1 ) visited_l output_l ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : ((Znth c visited_l_2 0) <> 0)) (PreH2 : (c >= 0)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start < 26)) (PreH9 : ((-1) <= c)) (PreH10 : (c < 26)) (PreH11 : (0 <= len)) (PreH12 : (len <= 26)) (PreH13 : ((Zlength (output_l_2)) = len)) (PreH14 : ((Zlength (next_l_2)) = 26)) (PreH15 : ((Zlength (prev_l_2)) = 26)) (PreH16 : ((Zlength (used_l_2)) = 26)) (PreH17 : ((Zlength (visited_l_2)) = 26)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH20 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH21 : (PathScanState next_l_2 prev_l_2 used_l_2 start c visited_l_2 output_l_2 )) ,
  TT && emp 
|--
  “ (TraversalState next_l_2 prev_l_2 used_l_2 (start + 1 ) visited_l_2 output_l_2 ) ”
  &&  emp
).

Definition solver_entail_wit_13_2_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : ((Znth c visited_l_2 0) <> 0)) (PreH2 : (c >= 0)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start < 26)) (PreH9 : ((-1) <= c)) (PreH10 : (c < 26)) (PreH11 : (0 <= len)) (PreH12 : (len <= 26)) (PreH13 : ((Zlength (output_l_2)) = len)) (PreH14 : ((Zlength (next_l_2)) = 26)) (PreH15 : ((Zlength (prev_l_2)) = 26)) (PreH16 : ((Zlength (used_l_2)) = 26)) (PreH17 : ((Zlength (visited_l_2)) = 26)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH20 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH21 : (PathScanState next_l_2 prev_l_2 used_l_2 start c visited_l_2 output_l_2 )) ,
  (TraversalState next_l_2 prev_l_2 used_l_2 (start + 1 ) visited_l_2 output_l_2 )
.

Definition solver_entail_wit_14_1 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l_2: (@list Z)) (prev_l_2: (@list Z)) (used_l_2: (@list Z)) (visited_l_2: (@list Z)) (output_l_2: (@list Z)) (start: Z) (c: Z) (len: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : (0 <= start)) (PreH6 : (start < 26)) (PreH7 : ((-1) <= c)) (PreH8 : (c < 26)) (PreH9 : (0 <= len)) (PreH10 : (len <= 26)) (PreH11 : ((Zlength (output_l_2)) = len)) (PreH12 : ((Zlength (next_l_2)) = 26)) (PreH13 : ((Zlength (prev_l_2)) = 26)) (PreH14 : ((Zlength (used_l_2)) = 26)) (PreH15 : ((Zlength (visited_l_2)) = 26)) (PreH16 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH17 : (TraversalState next_l_2 prev_l_2 used_l_2 (start + 1 ) visited_l_2 output_l_2 )) ,
  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l_2 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l_2 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l_2 )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l_2 )
  **  (CharArray.seg out_pre 0 len output_l_2 )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  EX (visited_l: (@list Z))  (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z))  (output_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= (start + 1 )) ” 
  &&  “ ((start + 1 ) <= 26) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 26) ” 
  &&  “ ((Zlength (output_l)) = len) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (visited_l)) = 26) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g n_pre next_l prev_l used_l ) ” 
  &&  “ (TraversalState next_l prev_l used_l (start + 1 ) visited_l output_l ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l_2: (@list Z)) (prev_l_2: (@list Z)) (used_l_2: (@list Z)) (visited_l_2: (@list Z)) (output_l_2: (@list Z)) (start: Z) (c: Z) (len: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : (0 <= start)) (PreH6 : (start < 26)) (PreH7 : ((-1) <= c)) (PreH8 : (c < 26)) (PreH9 : (0 <= len)) (PreH10 : (len <= 26)) (PreH11 : ((Zlength (output_l_2)) = len)) (PreH12 : ((Zlength (next_l_2)) = 26)) (PreH13 : ((Zlength (prev_l_2)) = 26)) (PreH14 : ((Zlength (used_l_2)) = 26)) (PreH15 : ((Zlength (visited_l_2)) = 26)) (PreH16 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH17 : (TraversalState next_l_2 prev_l_2 used_l_2 (start + 1 ) visited_l_2 output_l_2 )) ,
  TT && emp 
|--
  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26))) ”
  &&  emp
).

Definition solver_entail_wit_14_1_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l_2: (@list Z)) (prev_l_2: (@list Z)) (used_l_2: (@list Z)) (visited_l_2: (@list Z)) (output_l_2: (@list Z)) (start: Z) (c: Z) (len: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : (0 <= start)) (PreH6 : (start < 26)) (PreH7 : ((-1) <= c)) (PreH8 : (c < 26)) (PreH9 : (0 <= len)) (PreH10 : (len <= 26)) (PreH11 : ((Zlength (output_l_2)) = len)) (PreH12 : ((Zlength (next_l_2)) = 26)) (PreH13 : ((Zlength (prev_l_2)) = 26)) (PreH14 : ((Zlength (used_l_2)) = 26)) (PreH15 : ((Zlength (visited_l_2)) = 26)) (PreH16 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH17 : (TraversalState next_l_2 prev_l_2 used_l_2 (start + 1 ) visited_l_2 output_l_2 )) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))
.

Definition solver_entail_wit_14_1_split_goal_2 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l_2: (@list Z)) (prev_l_2: (@list Z)) (used_l_2: (@list Z)) (visited_l_2: (@list Z)) (output_l_2: (@list Z)) (start: Z) (c: Z) (len: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : (0 <= start)) (PreH6 : (start < 26)) (PreH7 : ((-1) <= c)) (PreH8 : (c < 26)) (PreH9 : (0 <= len)) (PreH10 : (len <= 26)) (PreH11 : ((Zlength (output_l_2)) = len)) (PreH12 : ((Zlength (next_l_2)) = 26)) (PreH13 : ((Zlength (prev_l_2)) = 26)) (PreH14 : ((Zlength (used_l_2)) = 26)) (PreH15 : ((Zlength (visited_l_2)) = 26)) (PreH16 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH17 : (TraversalState next_l_2 prev_l_2 used_l_2 (start + 1 ) visited_l_2 output_l_2 )) ,
  forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))
.

Definition solver_entail_wit_14_2 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (start: Z) (PreH1 : ((Znth start used_l_2 0) = 0)) (PreH2 : (start < 26)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start <= 26)) (PreH9 : (0 <= len)) (PreH10 : (len <= 26)) (PreH11 : ((Zlength (output_l_2)) = len)) (PreH12 : ((Zlength (next_l_2)) = 26)) (PreH13 : ((Zlength (prev_l_2)) = 26)) (PreH14 : ((Zlength (used_l_2)) = 26)) (PreH15 : ((Zlength (visited_l_2)) = 26)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH18 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH19 : (TraversalState next_l_2 prev_l_2 used_l_2 start visited_l_2 output_l_2 )) ,
  (IntArray.full ( &( "used" ) ) 26 used_l_2 )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l_2 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l_2 )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l_2 )
  **  (CharArray.seg out_pre 0 len output_l_2 )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  EX (visited_l: (@list Z))  (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z))  (output_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= (start + 1 )) ” 
  &&  “ ((start + 1 ) <= 26) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 26) ” 
  &&  “ ((Zlength (output_l)) = len) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (visited_l)) = 26) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g n_pre next_l prev_l used_l ) ” 
  &&  “ (TraversalState next_l prev_l used_l (start + 1 ) visited_l output_l ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (start: Z) (PreH1 : ((Znth start used_l_2 0) = 0)) (PreH2 : (start < 26)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start <= 26)) (PreH9 : (0 <= len)) (PreH10 : (len <= 26)) (PreH11 : ((Zlength (output_l_2)) = len)) (PreH12 : ((Zlength (next_l_2)) = 26)) (PreH13 : ((Zlength (prev_l_2)) = 26)) (PreH14 : ((Zlength (used_l_2)) = 26)) (PreH15 : ((Zlength (visited_l_2)) = 26)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH18 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH19 : (TraversalState next_l_2 prev_l_2 used_l_2 start visited_l_2 output_l_2 )) ,
  TT && emp 
|--
  “ (TraversalState next_l_2 prev_l_2 used_l_2 (start + 1 ) visited_l_2 output_l_2 ) ”
  &&  emp
).

Definition solver_entail_wit_14_2_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (start: Z) (PreH1 : ((Znth start used_l_2 0) = 0)) (PreH2 : (start < 26)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start <= 26)) (PreH9 : (0 <= len)) (PreH10 : (len <= 26)) (PreH11 : ((Zlength (output_l_2)) = len)) (PreH12 : ((Zlength (next_l_2)) = 26)) (PreH13 : ((Zlength (prev_l_2)) = 26)) (PreH14 : ((Zlength (used_l_2)) = 26)) (PreH15 : ((Zlength (visited_l_2)) = 26)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH18 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH19 : (TraversalState next_l_2 prev_l_2 used_l_2 start visited_l_2 output_l_2 )) ,
  (TraversalState next_l_2 prev_l_2 used_l_2 (start + 1 ) visited_l_2 output_l_2 )
.

Definition solver_entail_wit_14_3 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (start: Z) (PreH1 : ((Znth start prev_l_2 0) >= 0)) (PreH2 : ((Znth start used_l_2 0) <> 0)) (PreH3 : (start < 26)) (PreH4 : (n_pre = (Zlength (g)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= start)) (PreH9 : (start <= 26)) (PreH10 : (0 <= len)) (PreH11 : (len <= 26)) (PreH12 : ((Zlength (output_l_2)) = len)) (PreH13 : ((Zlength (next_l_2)) = 26)) (PreH14 : ((Zlength (prev_l_2)) = 26)) (PreH15 : ((Zlength (used_l_2)) = 26)) (PreH16 : ((Zlength (visited_l_2)) = 26)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH19 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH20 : (TraversalState next_l_2 prev_l_2 used_l_2 start visited_l_2 output_l_2 )) ,
  (IntArray.full ( &( "prev" ) ) 26 prev_l_2 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l_2 )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l_2 )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l_2 )
  **  (CharArray.seg out_pre 0 len output_l_2 )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  EX (visited_l: (@list Z))  (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z))  (output_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= (start + 1 )) ” 
  &&  “ ((start + 1 ) <= 26) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 26) ” 
  &&  “ ((Zlength (output_l)) = len) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (visited_l)) = 26) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g n_pre next_l prev_l used_l ) ” 
  &&  “ (TraversalState next_l prev_l used_l (start + 1 ) visited_l output_l ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (start: Z) (PreH1 : ((Znth start prev_l_2 0) >= 0)) (PreH2 : ((Znth start used_l_2 0) <> 0)) (PreH3 : (start < 26)) (PreH4 : (n_pre = (Zlength (g)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= start)) (PreH9 : (start <= 26)) (PreH10 : (0 <= len)) (PreH11 : (len <= 26)) (PreH12 : ((Zlength (output_l_2)) = len)) (PreH13 : ((Zlength (next_l_2)) = 26)) (PreH14 : ((Zlength (prev_l_2)) = 26)) (PreH15 : ((Zlength (used_l_2)) = 26)) (PreH16 : ((Zlength (visited_l_2)) = 26)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH19 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH20 : (TraversalState next_l_2 prev_l_2 used_l_2 start visited_l_2 output_l_2 )) ,
  TT && emp 
|--
  “ (TraversalState next_l_2 prev_l_2 used_l_2 (start + 1 ) visited_l_2 output_l_2 ) ”
  &&  emp
).

Definition solver_entail_wit_14_3_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (start: Z) (PreH1 : ((Znth start prev_l_2 0) >= 0)) (PreH2 : ((Znth start used_l_2 0) <> 0)) (PreH3 : (start < 26)) (PreH4 : (n_pre = (Zlength (g)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= start)) (PreH9 : (start <= 26)) (PreH10 : (0 <= len)) (PreH11 : (len <= 26)) (PreH12 : ((Zlength (output_l_2)) = len)) (PreH13 : ((Zlength (next_l_2)) = 26)) (PreH14 : ((Zlength (prev_l_2)) = 26)) (PreH15 : ((Zlength (used_l_2)) = 26)) (PreH16 : ((Zlength (visited_l_2)) = 26)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH19 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH20 : (TraversalState next_l_2 prev_l_2 used_l_2 start visited_l_2 output_l_2 )) ,
  (TraversalState next_l_2 prev_l_2 used_l_2 (start + 1 ) visited_l_2 output_l_2 )
.

Definition solver_entail_wit_15 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (start: Z) (PreH1 : (start >= 26)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= start)) (PreH7 : (start <= 26)) (PreH8 : (0 <= len)) (PreH9 : (len <= 26)) (PreH10 : ((Zlength (output_l_2)) = len)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : ((Zlength (visited_l_2)) = 26)) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH17 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH18 : (TraversalState next_l_2 prev_l_2 used_l_2 start visited_l_2 output_l_2 )) ,
  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l_2 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l_2 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l_2 )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l_2 )
  **  (CharArray.seg out_pre 0 len output_l_2 )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  EX (visited_l: (@list Z))  (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z))  (output_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 26) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 26) ” 
  &&  “ ((Zlength (output_l)) = len) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (visited_l)) = 26) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g n_pre next_l prev_l used_l ) ” 
  &&  “ (TraversalState next_l prev_l used_l 26 visited_l output_l ) ” 
  &&  “ (CoverageScanState used_l visited_l 0 ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (start: Z) (PreH1 : (start >= 26)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= start)) (PreH7 : (start <= 26)) (PreH8 : (0 <= len)) (PreH9 : (len <= 26)) (PreH10 : ((Zlength (output_l_2)) = len)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : ((Zlength (visited_l_2)) = 26)) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH17 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH18 : (TraversalState next_l_2 prev_l_2 used_l_2 start visited_l_2 output_l_2 )) ,
  TT && emp 
|--
  “ (CoverageScanState used_l_2 visited_l_2 0 ) ” 
  &&  “ (TraversalState next_l_2 prev_l_2 used_l_2 26 visited_l_2 output_l_2 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26))) ”
  &&  emp
).

Definition solver_entail_wit_15_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (start: Z) (PreH1 : (start >= 26)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= start)) (PreH7 : (start <= 26)) (PreH8 : (0 <= len)) (PreH9 : (len <= 26)) (PreH10 : ((Zlength (output_l_2)) = len)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : ((Zlength (visited_l_2)) = 26)) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH17 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH18 : (TraversalState next_l_2 prev_l_2 used_l_2 start visited_l_2 output_l_2 )) ,
  (CoverageScanState used_l_2 visited_l_2 0 )
.

Definition solver_entail_wit_15_split_goal_2 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (start: Z) (PreH1 : (start >= 26)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= start)) (PreH7 : (start <= 26)) (PreH8 : (0 <= len)) (PreH9 : (len <= 26)) (PreH10 : ((Zlength (output_l_2)) = len)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : ((Zlength (visited_l_2)) = 26)) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH17 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH18 : (TraversalState next_l_2 prev_l_2 used_l_2 start visited_l_2 output_l_2 )) ,
  (TraversalState next_l_2 prev_l_2 used_l_2 26 visited_l_2 output_l_2 )
.

Definition solver_entail_wit_15_split_goal_3 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (start: Z) (PreH1 : (start >= 26)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= start)) (PreH7 : (start <= 26)) (PreH8 : (0 <= len)) (PreH9 : (len <= 26)) (PreH10 : ((Zlength (output_l_2)) = len)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : ((Zlength (visited_l_2)) = 26)) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH17 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH18 : (TraversalState next_l_2 prev_l_2 used_l_2 start visited_l_2 output_l_2 )) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))
.

Definition solver_entail_wit_15_split_goal_4 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (start: Z) (PreH1 : (start >= 26)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= start)) (PreH7 : (start <= 26)) (PreH8 : (0 <= len)) (PreH9 : (len <= 26)) (PreH10 : ((Zlength (output_l_2)) = len)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : ((Zlength (visited_l_2)) = 26)) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l_2) ((-1)))) /\ ((Znth (k_3) (next_l_2) ((-1))) < 26)))) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l_2) ((-1)))) /\ ((Znth (k_4) (prev_l_2) ((-1))) < 26)))) (PreH17 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH18 : (TraversalState next_l_2 prev_l_2 used_l_2 start visited_l_2 output_l_2 )) ,
  forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))
.

Definition solver_entail_wit_16 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (PreH1 : (c >= 26)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c <= 26)) (PreH8 : (0 <= len)) (PreH9 : (len <= 26)) (PreH10 : ((Zlength (output_l_2)) = len)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : ((Zlength (visited_l_2)) = 26)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH17 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH18 : (TraversalState next_l_2 prev_l_2 used_l_2 26 visited_l_2 output_l_2 )) (PreH19 : (CoverageScanState used_l_2 visited_l_2 c )) ,
  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l_2 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l_2 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l_2 )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l_2 )
  **  (CharArray.seg out_pre 0 len output_l_2 )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  EX (next_l: (@list Z))  (prev_l: (@list Z))  (used_l: (@list Z))  (visited_l: (@list Z))  (output_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 26) ” 
  &&  “ ((Zlength (output_l)) = len) ” 
  &&  “ (SuccessfulTraversal g next_l prev_l used_l visited_l output_l ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (PreH1 : (c >= 26)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c <= 26)) (PreH8 : (0 <= len)) (PreH9 : (len <= 26)) (PreH10 : ((Zlength (output_l_2)) = len)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : ((Zlength (visited_l_2)) = 26)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH17 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH18 : (TraversalState next_l_2 prev_l_2 used_l_2 26 visited_l_2 output_l_2 )) (PreH19 : (CoverageScanState used_l_2 visited_l_2 c )) ,
  TT && emp 
|--
  “ (SuccessfulTraversal g next_l_2 prev_l_2 used_l_2 visited_l_2 output_l_2 ) ”
  &&  emp
).

Definition solver_entail_wit_16_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (PreH1 : (c >= 26)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c <= 26)) (PreH8 : (0 <= len)) (PreH9 : (len <= 26)) (PreH10 : ((Zlength (output_l_2)) = len)) (PreH11 : ((Zlength (next_l_2)) = 26)) (PreH12 : ((Zlength (prev_l_2)) = 26)) (PreH13 : ((Zlength (used_l_2)) = 26)) (PreH14 : ((Zlength (visited_l_2)) = 26)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH17 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH18 : (TraversalState next_l_2 prev_l_2 used_l_2 26 visited_l_2 output_l_2 )) (PreH19 : (CoverageScanState used_l_2 visited_l_2 c )) ,
  (SuccessfulTraversal g next_l_2 prev_l_2 used_l_2 visited_l_2 output_l_2 )
.

Definition solver_entail_wit_17_1 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (PreH1 : ((Znth c used_l_2 0) = 0)) (PreH2 : (c < 26)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c <= 26)) (PreH9 : (0 <= len)) (PreH10 : (len <= 26)) (PreH11 : ((Zlength (output_l_2)) = len)) (PreH12 : ((Zlength (next_l_2)) = 26)) (PreH13 : ((Zlength (prev_l_2)) = 26)) (PreH14 : ((Zlength (used_l_2)) = 26)) (PreH15 : ((Zlength (visited_l_2)) = 26)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH18 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH19 : (TraversalState next_l_2 prev_l_2 used_l_2 26 visited_l_2 output_l_2 )) (PreH20 : (CoverageScanState used_l_2 visited_l_2 c )) ,
  (IntArray.full ( &( "used" ) ) 26 used_l_2 )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l_2 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l_2 )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l_2 )
  **  (CharArray.seg out_pre 0 len output_l_2 )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  EX (visited_l: (@list Z))  (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z))  (output_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= (c + 1 )) ” 
  &&  “ ((c + 1 ) <= 26) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 26) ” 
  &&  “ ((Zlength (output_l)) = len) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (visited_l)) = 26) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g n_pre next_l prev_l used_l ) ” 
  &&  “ (TraversalState next_l prev_l used_l 26 visited_l output_l ) ” 
  &&  “ (CoverageScanState used_l visited_l (c + 1 ) ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (PreH1 : ((Znth c used_l_2 0) = 0)) (PreH2 : (c < 26)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c <= 26)) (PreH9 : (0 <= len)) (PreH10 : (len <= 26)) (PreH11 : ((Zlength (output_l_2)) = len)) (PreH12 : ((Zlength (next_l_2)) = 26)) (PreH13 : ((Zlength (prev_l_2)) = 26)) (PreH14 : ((Zlength (used_l_2)) = 26)) (PreH15 : ((Zlength (visited_l_2)) = 26)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH18 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH19 : (TraversalState next_l_2 prev_l_2 used_l_2 26 visited_l_2 output_l_2 )) (PreH20 : (CoverageScanState used_l_2 visited_l_2 c )) ,
  TT && emp 
|--
  “ (CoverageScanState used_l_2 visited_l_2 (c + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_17_1_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (PreH1 : ((Znth c used_l_2 0) = 0)) (PreH2 : (c < 26)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c <= 26)) (PreH9 : (0 <= len)) (PreH10 : (len <= 26)) (PreH11 : ((Zlength (output_l_2)) = len)) (PreH12 : ((Zlength (next_l_2)) = 26)) (PreH13 : ((Zlength (prev_l_2)) = 26)) (PreH14 : ((Zlength (used_l_2)) = 26)) (PreH15 : ((Zlength (visited_l_2)) = 26)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH18 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH19 : (TraversalState next_l_2 prev_l_2 used_l_2 26 visited_l_2 output_l_2 )) (PreH20 : (CoverageScanState used_l_2 visited_l_2 c )) ,
  (CoverageScanState used_l_2 visited_l_2 (c + 1 ) )
.

Definition solver_entail_wit_17_2 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (PreH1 : ((Znth c visited_l_2 0) <> 0)) (PreH2 : ((Znth c used_l_2 0) <> 0)) (PreH3 : (c < 26)) (PreH4 : (n_pre = (Zlength (g)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c <= 26)) (PreH10 : (0 <= len)) (PreH11 : (len <= 26)) (PreH12 : ((Zlength (output_l_2)) = len)) (PreH13 : ((Zlength (next_l_2)) = 26)) (PreH14 : ((Zlength (prev_l_2)) = 26)) (PreH15 : ((Zlength (used_l_2)) = 26)) (PreH16 : ((Zlength (visited_l_2)) = 26)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH19 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH20 : (TraversalState next_l_2 prev_l_2 used_l_2 26 visited_l_2 output_l_2 )) (PreH21 : (CoverageScanState used_l_2 visited_l_2 c )) ,
  (IntArray.full ( &( "visited" ) ) 26 visited_l_2 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l_2 )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l_2 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l_2 )
  **  (CharArray.seg out_pre 0 len output_l_2 )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  EX (visited_l: (@list Z))  (used_l: (@list Z))  (prev_l: (@list Z))  (next_l: (@list Z))  (output_l: (@list Z)) ,
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= (c + 1 )) ” 
  &&  “ ((c + 1 ) <= 26) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 26) ” 
  &&  “ ((Zlength (output_l)) = len) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (visited_l)) = 26) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g n_pre next_l prev_l used_l ) ” 
  &&  “ (TraversalState next_l prev_l used_l 26 visited_l output_l ) ” 
  &&  “ (CoverageScanState used_l visited_l (c + 1 ) ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
) \/
(
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (PreH1 : ((Znth c visited_l_2 0) <> 0)) (PreH2 : ((Znth c used_l_2 0) <> 0)) (PreH3 : (c < 26)) (PreH4 : (n_pre = (Zlength (g)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c <= 26)) (PreH10 : (0 <= len)) (PreH11 : (len <= 26)) (PreH12 : ((Zlength (output_l_2)) = len)) (PreH13 : ((Zlength (next_l_2)) = 26)) (PreH14 : ((Zlength (prev_l_2)) = 26)) (PreH15 : ((Zlength (used_l_2)) = 26)) (PreH16 : ((Zlength (visited_l_2)) = 26)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH19 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH20 : (TraversalState next_l_2 prev_l_2 used_l_2 26 visited_l_2 output_l_2 )) (PreH21 : (CoverageScanState used_l_2 visited_l_2 c )) ,
  TT && emp 
|--
  “ (CoverageScanState used_l_2 visited_l_2 (c + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_17_2_split_goal_1 := 
forall (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l_2: (@list Z)) (used_l_2: (@list Z)) (prev_l_2: (@list Z)) (next_l_2: (@list Z)) (output_l_2: (@list Z)) (len: Z) (c: Z) (PreH1 : ((Znth c visited_l_2 0) <> 0)) (PreH2 : ((Znth c used_l_2 0) <> 0)) (PreH3 : (c < 26)) (PreH4 : (n_pre = (Zlength (g)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c <= 26)) (PreH10 : (0 <= len)) (PreH11 : (len <= 26)) (PreH12 : ((Zlength (output_l_2)) = len)) (PreH13 : ((Zlength (next_l_2)) = 26)) (PreH14 : ((Zlength (prev_l_2)) = 26)) (PreH15 : ((Zlength (used_l_2)) = 26)) (PreH16 : ((Zlength (visited_l_2)) = 26)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l_2) ((-1)))) /\ ((Znth (k) (next_l_2) ((-1))) < 26)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l_2) ((-1)))) /\ ((Znth (k_2) (prev_l_2) ((-1))) < 26)))) (PreH19 : (GraphBuildState g n_pre next_l_2 prev_l_2 used_l_2 )) (PreH20 : (TraversalState next_l_2 prev_l_2 used_l_2 26 visited_l_2 output_l_2 )) (PreH21 : (CoverageScanState used_l_2 visited_l_2 c )) ,
  (CoverageScanState used_l_2 visited_l_2 (c + 1 ) )
.

Definition solver_return_wit_1 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l: (@list Z)) (prev_l: (@list Z)) (used_l: (@list Z)) (visited_l: (@list Z)) (output_l: (@list Z)) (len: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : (0 <= len)) (PreH6 : (len <= 26)) (PreH7 : ((Zlength (output_l)) = len)) (PreH8 : (SuccessfulTraversal g next_l prev_l used_l visited_l output_l )) ,
  (CharArray.seg out_pre 0 (len + 1 ) (app (output_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (len + 1 ) 64 )
  **  (CharPtrArray2.full words_pre n_pre rows )
|--
  EX (result: (@list Z)) ,
  “ (1 = 1) ” 
  &&  “ (Spec g (Some (result)) ) ” 
  &&  “ ((Zlength (result)) < 64) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.full out_pre ((Zlength (result)) + 1 ) (app (result) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (result)) + 1 ) 64 )
) \/
(
forall (out_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l: (@list Z)) (prev_l: (@list Z)) (used_l: (@list Z)) (visited_l: (@list Z)) (output_l: (@list Z)) (len: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : (0 <= len)) (PreH6 : (len <= 26)) (PreH7 : ((Zlength (output_l)) = len)) (PreH8 : (SuccessfulTraversal g next_l prev_l used_l visited_l output_l )) ,
  (CharArray.seg out_pre 0 (len + 1 ) (app (output_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (len + 1 ) 64 )
|--
  EX (result: (@list Z)) ,
  “ (Spec g (Some (result)) ) ” 
  &&  “ ((Zlength (result)) < 64) ”
  &&  (CharArray.full out_pre ((Zlength (result)) + 1 ) (app (result) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (result)) + 1 ) 64 )
).

Definition solver_return_wit_2 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (c: Z) (PreH1 : ((Znth c visited_l 0) = 0)) (PreH2 : ((Znth c used_l 0) <> 0)) (PreH3 : (c < 26)) (PreH4 : (n_pre = (Zlength (g)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c <= 26)) (PreH10 : (0 <= len)) (PreH11 : (len <= 26)) (PreH12 : ((Zlength (output_l)) = len)) (PreH13 : ((Zlength (next_l)) = 26)) (PreH14 : ((Zlength (prev_l)) = 26)) (PreH15 : ((Zlength (used_l)) = 26)) (PreH16 : ((Zlength (visited_l)) = 26)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH19 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH20 : (TraversalState next_l prev_l used_l 26 visited_l output_l )) (PreH21 : (CoverageScanState used_l visited_l c )) ,
  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  EX (partial: (@list Z))  (written: Z) ,
  “ (0 = 0) ” 
  &&  “ (Spec g None ) ” 
  &&  “ (0 <= written) ” 
  &&  “ (written <= 26) ” 
  &&  “ ((Zlength (partial)) = written) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.full out_pre written partial )
  **  (CharArray.undef_seg out_pre written 64 )
) \/
(
forall (out_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (c: Z) (PreH1 : ((Znth c visited_l 0) = 0)) (PreH2 : ((Znth c used_l 0) <> 0)) (PreH3 : (c < 26)) (PreH4 : (n_pre = (Zlength (g)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c <= 26)) (PreH10 : (0 <= len)) (PreH11 : (len <= 26)) (PreH12 : ((Zlength (output_l)) = len)) (PreH13 : ((Zlength (next_l)) = 26)) (PreH14 : ((Zlength (prev_l)) = 26)) (PreH15 : ((Zlength (used_l)) = 26)) (PreH16 : ((Zlength (visited_l)) = 26)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH19 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH20 : (TraversalState next_l prev_l used_l 26 visited_l output_l )) (PreH21 : (CoverageScanState used_l visited_l c )) ,
  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  EX (partial: (@list Z)) ,
  “ (Spec g None ) ” 
  &&  “ (0 <= (Zlength (partial))) ” 
  &&  “ ((Zlength (partial)) <= 26) ”
  &&  (CharArray.full out_pre (Zlength (partial)) partial )
  **  (CharArray.undef_seg out_pre (Zlength (partial)) 64 )
).

Definition solver_return_wit_3 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth last next_l 0) <> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH2 : ((Znth last next_l 0) >= 0)) (PreH3 : (last >= 0)) (PreH4 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH6 : (last <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (z <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (last >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (z >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH15 : (n_pre = (Zlength (g)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 100000)) (PreH18 : ((Zlength (rows)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH20 : (0 <= z)) (PreH21 : (z < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH24 : ((-1) <= last)) (PreH25 : (last < 26)) (PreH26 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH27 : ((Zlength (next_l)) = 26)) (PreH28 : ((Zlength (prev_l)) = 26)) (PreH29 : ((Zlength (used_l)) = 26)) (PreH30 : ((Zlength (seen_l)) = 26)) (PreH31 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH32 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH33 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH34 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH35 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  EX (partial: (@list Z))  (written: Z) ,
  “ (0 = 0) ” 
  &&  “ (Spec g None ) ” 
  &&  “ (0 <= written) ” 
  &&  “ (written <= 26) ” 
  &&  “ ((Zlength (partial)) = written) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.full out_pre written partial )
  **  (CharArray.undef_seg out_pre written 64 )
) \/
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth last next_l 0) <> ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH2 : ((Znth last next_l 0) >= 0)) (PreH3 : (last >= 0)) (PreH4 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH6 : (last <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (z <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (last >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (z >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH15 : (n_pre = (Zlength (g)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 100000)) (PreH18 : ((Zlength (rows)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH20 : (0 <= z)) (PreH21 : (z < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH24 : ((-1) <= last)) (PreH25 : (last < 26)) (PreH26 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH27 : ((Zlength (next_l)) = 26)) (PreH28 : ((Zlength (prev_l)) = 26)) (PreH29 : ((Zlength (used_l)) = 26)) (PreH30 : ((Zlength (seen_l)) = 26)) (PreH31 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH32 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH33 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH34 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH35 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  EX (partial: (@list Z)) ,
  “ (Spec g None ) ” 
  &&  “ (0 <= (Zlength (partial))) ” 
  &&  “ ((Zlength (partial)) <= 26) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.full out_pre (Zlength (partial)) partial )
  **  (CharArray.undef_seg out_pre (Zlength (partial)) 64 )
).

Definition solver_return_wit_4 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) <> last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0)) (PreH3 : ((Znth last next_l 0) < 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l)) = 26)) (PreH29 : ((Zlength (prev_l)) = 26)) (PreH30 : ((Zlength (used_l)) = 26)) (PreH31 : ((Zlength (seen_l)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  EX (partial: (@list Z))  (written: Z) ,
  “ (0 = 0) ” 
  &&  “ (Spec g None ) ” 
  &&  “ (0 <= written) ” 
  &&  “ (written <= 26) ” 
  &&  “ ((Zlength (partial)) = written) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.full out_pre written partial )
  **  (CharArray.undef_seg out_pre written 64 )
) \/
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) <> last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0)) (PreH3 : ((Znth last next_l 0) < 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l)) = 26)) (PreH29 : ((Zlength (prev_l)) = 26)) (PreH30 : ((Zlength (used_l)) = 26)) (PreH31 : ((Zlength (seen_l)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  EX (partial: (@list Z)) ,
  “ (Spec g None ) ” 
  &&  “ (0 <= (Zlength (partial))) ” 
  &&  “ ((Zlength (partial)) <= 26) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.full out_pre (Zlength (partial)) partial )
  **  (CharArray.undef_seg out_pre (Zlength (partial)) 64 )
).

Definition solver_return_wit_5 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) <> last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0)) (PreH3 : ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH4 : ((Znth last next_l 0) >= 0)) (PreH5 : (last >= 0)) (PreH6 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH7 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH8 : (last <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (z <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (last >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (z >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH17 : (n_pre = (Zlength (g)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (rows)) = n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH22 : (0 <= z)) (PreH23 : (z < n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH26 : ((-1) <= last)) (PreH27 : (last < 26)) (PreH28 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH29 : ((Zlength (next_l)) = 26)) (PreH30 : ((Zlength (prev_l)) = 26)) (PreH31 : ((Zlength (used_l)) = 26)) (PreH32 : ((Zlength (seen_l)) = 26)) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH34 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH35 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH36 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH37 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  EX (partial: (@list Z))  (written: Z) ,
  “ (0 = 0) ” 
  &&  “ (Spec g None ) ” 
  &&  “ (0 <= written) ” 
  &&  “ (written <= 26) ” 
  &&  “ ((Zlength (partial)) = written) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.full out_pre written partial )
  **  (CharArray.undef_seg out_pre written 64 )
) \/
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) <> last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0)) (PreH3 : ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH4 : ((Znth last next_l 0) >= 0)) (PreH5 : (last >= 0)) (PreH6 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH7 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH8 : (last <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (z <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (last >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (z >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH17 : (n_pre = (Zlength (g)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (rows)) = n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH22 : (0 <= z)) (PreH23 : (z < n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH26 : ((-1) <= last)) (PreH27 : (last < 26)) (PreH28 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH29 : ((Zlength (next_l)) = 26)) (PreH30 : ((Zlength (prev_l)) = 26)) (PreH31 : ((Zlength (used_l)) = 26)) (PreH32 : ((Zlength (seen_l)) = 26)) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH34 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH35 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH36 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH37 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  EX (partial: (@list Z)) ,
  “ (Spec g None ) ” 
  &&  “ (0 <= (Zlength (partial))) ” 
  &&  “ ((Zlength (partial)) <= 26) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.full out_pre (Zlength (partial)) partial )
  **  (CharArray.undef_seg out_pre (Zlength (partial)) 64 )
).

Definition solver_return_wit_6 := 
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH2 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH3 : (last <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (z <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (last >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (z >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH12 : (n_pre = (Zlength (g)))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100000)) (PreH15 : ((Zlength (rows)) = n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH17 : (0 <= z)) (PreH18 : (z < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH21 : ((-1) <= last)) (PreH22 : (last < 26)) (PreH23 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH24 : ((Zlength (next_l)) = 26)) (PreH25 : ((Zlength (prev_l)) = 26)) (PreH26 : ((Zlength (used_l)) = 26)) (PreH27 : ((Zlength (seen_l)) = 26)) (PreH28 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH29 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH30 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH31 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH32 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) <> 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  EX (partial: (@list Z))  (written: Z) ,
  “ (0 = 0) ” 
  &&  “ (Spec g None ) ” 
  &&  “ (0 <= written) ” 
  &&  “ (written <= 26) ” 
  &&  “ ((Zlength (partial)) = written) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.full out_pre written partial )
  **  (CharArray.undef_seg out_pre written 64 )
) \/
(
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH2 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH3 : (last <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (z <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (last >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (z >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH12 : (n_pre = (Zlength (g)))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100000)) (PreH15 : ((Zlength (rows)) = n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH17 : (0 <= z)) (PreH18 : (z < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH21 : ((-1) <= last)) (PreH22 : (last < 26)) (PreH23 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH24 : ((Zlength (next_l)) = 26)) (PreH25 : ((Zlength (prev_l)) = 26)) (PreH26 : ((Zlength (used_l)) = 26)) (PreH27 : ((Zlength (seen_l)) = 26)) (PreH28 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH29 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH30 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH31 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH32 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) <> 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  EX (partial: (@list Z)) ,
  “ (Spec g None ) ” 
  &&  “ (0 <= (Zlength (partial))) ” 
  &&  “ ((Zlength (partial)) <= 26) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.full out_pre (Zlength (partial)) partial )
  **  (CharArray.undef_seg out_pre (Zlength (partial)) 64 )
).

Definition solver_partial_solve_wit_1 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l: (@list Z)) (prev_prefix: (@list Z)) (next_prefix: (@list Z)) (i: Z) (PreH1 : (i < 26)) (PreH2 : (Pre g )) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= i)) (PreH10 : (i <= 26)) (PreH11 : ((Zlength (next_prefix)) = i)) (PreH12 : ((Zlength (prev_prefix)) = i)) (PreH13 : (InitState next_prefix prev_prefix used_l )) ,
  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.seg ( &( "next" ) ) 0 i next_prefix )
  **  (IntArray.undef_seg ( &( "next" ) ) i 26 )
  **  (IntArray.seg ( &( "prev" ) ) 0 i prev_prefix )
  **  (IntArray.undef_seg ( &( "prev" ) ) i 26 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
|--
  “ (i < 26) ” 
  &&  “ (Pre g ) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 26) ” 
  &&  “ ((Zlength (next_prefix)) = i) ” 
  &&  “ ((Zlength (prev_prefix)) = i) ” 
  &&  “ (InitState next_prefix prev_prefix used_l ) ”
  &&  (((( &( "prev" ) ) + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "prev" ) ) (i + 1 ) 26 )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.seg ( &( "next" ) ) 0 i next_prefix )
  **  (IntArray.undef_seg ( &( "next" ) ) i 26 )
  **  (IntArray.seg ( &( "prev" ) ) 0 i prev_prefix )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
.

Definition solver_partial_solve_wit_2 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (used_l: (@list Z)) (prev_prefix: (@list Z)) (next_prefix: (@list Z)) (i: Z) (PreH1 : (i < 26)) (PreH2 : (Pre g )) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH8 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH9 : (0 <= i)) (PreH10 : (i <= 26)) (PreH11 : ((Zlength (next_prefix)) = i)) (PreH12 : ((Zlength (prev_prefix)) = i)) (PreH13 : (InitState next_prefix prev_prefix used_l )) ,
  (IntArray.seg ( &( "prev" ) ) 0 (i + 1 ) (app (prev_prefix) ((cons ((-1)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "prev" ) ) (i + 1 ) 26 )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.seg ( &( "next" ) ) 0 i next_prefix )
  **  (IntArray.undef_seg ( &( "next" ) ) i 26 )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
|--
  “ (i < 26) ” 
  &&  “ (Pre g ) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 26) ” 
  &&  “ ((Zlength (next_prefix)) = i) ” 
  &&  “ ((Zlength (prev_prefix)) = i) ” 
  &&  “ (InitState next_prefix prev_prefix used_l ) ”
  &&  (((( &( "next" ) ) + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "next" ) ) (i + 1 ) 26 )
  **  (IntArray.seg ( &( "prev" ) ) 0 (i + 1 ) (app (prev_prefix) ((cons ((-1)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "prev" ) ) (i + 1 ) 26 )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.seg ( &( "next" ) ) 0 i next_prefix )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
.

Definition solver_partial_solve_wit_3 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : (0 <= z)) (PreH7 : (z < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH10 : ((-1) <= last)) (PreH11 : (last < 26)) (PreH12 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH13 : ((Zlength (next_l)) = 26)) (PreH14 : ((Zlength (prev_l)) = 26)) (PreH15 : ((Zlength (used_l)) = 26)) (PreH16 : ((Zlength (seen_l)) = 26)) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH19 : (WordScanState g z i next_l prev_l used_l seen_l last )) ,
  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
|--
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z i next_l prev_l used_l seen_l last ) ”
  &&  (((saved_s + (i * sizeof(CHAR)))) # Char  |-> (Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0))
  **  (CharArray.missing_i saved_s i 0 ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
.

Definition solver_partial_solve_wit_4 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH6 : (0 <= z)) (PreH7 : (z < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH10 : ((-1) <= last)) (PreH11 : (last < 26)) (PreH12 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH13 : ((Zlength (next_l)) = 26)) (PreH14 : ((Zlength (prev_l)) = 26)) (PreH15 : ((Zlength (used_l)) = 26)) (PreH16 : ((Zlength (seen_l)) = 26)) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH19 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH20 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
|--
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z i next_l prev_l used_l seen_l last ) ” 
  &&  “ ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0) ”
  &&  (((saved_s + (i * sizeof(CHAR)))) # Char  |-> (Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0))
  **  (CharArray.missing_i saved_s i 0 ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
.

Definition solver_partial_solve_wit_5 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH2 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH3 : (last <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (z <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (last >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (z >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH12 : (n_pre = (Zlength (g)))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100000)) (PreH15 : ((Zlength (rows)) = n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH17 : (0 <= z)) (PreH18 : (z < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH21 : ((-1) <= last)) (PreH22 : (last < 26)) (PreH23 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH24 : ((Zlength (next_l)) = 26)) (PreH25 : ((Zlength (prev_l)) = 26)) (PreH26 : ((Zlength (used_l)) = 26)) (PreH27 : ((Zlength (seen_l)) = 26)) (PreH28 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH29 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH30 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH31 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
|--
  “ (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ (last <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (z <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (last >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (z >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 )) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z i next_l prev_l used_l seen_l last ) ” 
  &&  “ ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0) ”
  &&  (((( &( "used" ) ) + (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "used" ) ) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) 0 26 used_l )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
.

Definition solver_partial_solve_wit_6 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH2 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH3 : (last <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (z <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (last >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (z >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH12 : (n_pre = (Zlength (g)))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100000)) (PreH15 : ((Zlength (rows)) = n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH17 : (0 <= z)) (PreH18 : (z < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH21 : ((-1) <= last)) (PreH22 : (last < 26)) (PreH23 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH24 : ((Zlength (next_l)) = 26)) (PreH25 : ((Zlength (prev_l)) = 26)) (PreH26 : ((Zlength (used_l)) = 26)) (PreH27 : ((Zlength (seen_l)) = 26)) (PreH28 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH29 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH30 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH31 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) ,
  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "seen" ) ) 26 seen_l )
|--
  “ (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ (last <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (z <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (last >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (z >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 )) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z i next_l prev_l used_l seen_l last ) ” 
  &&  “ ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0) ”
  &&  (((( &( "seen" ) ) + (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) * sizeof(INT)))) # Int  |-> (Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0))
  **  (IntArray.missing_i ( &( "seen" ) ) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) 0 26 seen_l )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
.

Definition solver_partial_solve_wit_7 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH2 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH3 : (last <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (z <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (last >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (z >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH12 : (n_pre = (Zlength (g)))) (PreH13 : (1 <= n_pre)) (PreH14 : (n_pre <= 100000)) (PreH15 : ((Zlength (rows)) = n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH17 : (0 <= z)) (PreH18 : (z < n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH21 : ((-1) <= last)) (PreH22 : (last < 26)) (PreH23 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH24 : ((Zlength (next_l)) = 26)) (PreH25 : ((Zlength (prev_l)) = 26)) (PreH26 : ((Zlength (used_l)) = 26)) (PreH27 : ((Zlength (seen_l)) = 26)) (PreH28 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH29 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH30 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH31 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH32 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "seen" ) ) 26 seen_l )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
|--
  “ (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ (last <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (z <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (last >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (z >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 )) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z i next_l prev_l used_l seen_l last ) ” 
  &&  “ ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0) ” 
  &&  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0) ”
  &&  (((( &( "seen" ) ) + (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "seen" ) ) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) 0 26 seen_l )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
.

Definition solver_partial_solve_wit_8 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : (last >= 0)) (PreH2 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH4 : (last <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (z <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (last >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (z >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH13 : (n_pre = (Zlength (g)))) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : ((Zlength (rows)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH18 : (0 <= z)) (PreH19 : (z < n_pre)) (PreH20 : (0 <= i)) (PreH21 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH22 : ((-1) <= last)) (PreH23 : (last < 26)) (PreH24 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH25 : ((Zlength (next_l)) = 26)) (PreH26 : ((Zlength (prev_l)) = 26)) (PreH27 : ((Zlength (used_l)) = 26)) (PreH28 : ((Zlength (seen_l)) = 26)) (PreH29 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH30 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH31 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH32 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH33 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
|--
  “ (last >= 0) ” 
  &&  “ (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ (last <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (z <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (last >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (z >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 )) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z i next_l prev_l used_l seen_l last ) ” 
  &&  “ ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0) ” 
  &&  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0) ”
  &&  (((( &( "next" ) ) + (last * sizeof(INT)))) # Int  |-> (Znth last next_l 0))
  **  (IntArray.missing_i ( &( "next" ) ) last 0 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
.

Definition solver_partial_solve_wit_9 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth last next_l 0) >= 0)) (PreH2 : (last >= 0)) (PreH3 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH4 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH5 : (last <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (z <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (last >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (z >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH14 : (n_pre = (Zlength (g)))) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 100000)) (PreH17 : ((Zlength (rows)) = n_pre)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH19 : (0 <= z)) (PreH20 : (z < n_pre)) (PreH21 : (0 <= i)) (PreH22 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH23 : ((-1) <= last)) (PreH24 : (last < 26)) (PreH25 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH26 : ((Zlength (next_l)) = 26)) (PreH27 : ((Zlength (prev_l)) = 26)) (PreH28 : ((Zlength (used_l)) = 26)) (PreH29 : ((Zlength (seen_l)) = 26)) (PreH30 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH31 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH32 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH33 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH34 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
|--
  “ ((Znth last next_l 0) >= 0) ” 
  &&  “ (last >= 0) ” 
  &&  “ (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ (last <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (z <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (last >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (z >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 )) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z i next_l prev_l used_l seen_l last ) ” 
  &&  “ ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0) ” 
  &&  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0) ”
  &&  (((( &( "next" ) ) + (last * sizeof(INT)))) # Int  |-> (Znth last next_l 0))
  **  (IntArray.missing_i ( &( "next" ) ) last 0 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
.

Definition solver_partial_solve_wit_10 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH2 : ((Znth last next_l 0) >= 0)) (PreH3 : (last >= 0)) (PreH4 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH6 : (last <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (z <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (last >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (z >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH15 : (n_pre = (Zlength (g)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 100000)) (PreH18 : ((Zlength (rows)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH20 : (0 <= z)) (PreH21 : (z < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH24 : ((-1) <= last)) (PreH25 : (last < 26)) (PreH26 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH27 : ((Zlength (next_l)) = 26)) (PreH28 : ((Zlength (prev_l)) = 26)) (PreH29 : ((Zlength (used_l)) = 26)) (PreH30 : ((Zlength (seen_l)) = 26)) (PreH31 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH32 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH33 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH34 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH35 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
|--
  “ ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ ((Znth last next_l 0) >= 0) ” 
  &&  “ (last >= 0) ” 
  &&  “ (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ (last <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (z <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (last >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (z >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 )) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z i next_l prev_l used_l seen_l last ) ” 
  &&  “ ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0) ” 
  &&  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0) ”
  &&  (((( &( "prev" ) ) + (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) * sizeof(INT)))) # Int  |-> (Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0))
  **  (IntArray.missing_i ( &( "prev" ) ) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) 0 26 prev_l )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
.

Definition solver_partial_solve_wit_11 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth last next_l 0) < 0)) (PreH2 : (last >= 0)) (PreH3 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH4 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH5 : (last <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (z <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (last >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (z >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH14 : (n_pre = (Zlength (g)))) (PreH15 : (1 <= n_pre)) (PreH16 : (n_pre <= 100000)) (PreH17 : ((Zlength (rows)) = n_pre)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH19 : (0 <= z)) (PreH20 : (z < n_pre)) (PreH21 : (0 <= i)) (PreH22 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH23 : ((-1) <= last)) (PreH24 : (last < 26)) (PreH25 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH26 : ((Zlength (next_l)) = 26)) (PreH27 : ((Zlength (prev_l)) = 26)) (PreH28 : ((Zlength (used_l)) = 26)) (PreH29 : ((Zlength (seen_l)) = 26)) (PreH30 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH31 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH32 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH33 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH34 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
|--
  “ ((Znth last next_l 0) < 0) ” 
  &&  “ (last >= 0) ” 
  &&  “ (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ (last <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (z <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (last >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (z >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 )) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z i next_l prev_l used_l seen_l last ) ” 
  &&  “ ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0) ” 
  &&  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0) ”
  &&  (((( &( "prev" ) ) + (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) * sizeof(INT)))) # Int  |-> (Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0))
  **  (IntArray.missing_i ( &( "prev" ) ) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) 0 26 prev_l )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
.

Definition solver_partial_solve_wit_12 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0)) (PreH2 : ((Znth last next_l 0) < 0)) (PreH3 : (last >= 0)) (PreH4 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH6 : (last <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (z <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (last >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (z >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH15 : (n_pre = (Zlength (g)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 100000)) (PreH18 : ((Zlength (rows)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH20 : (0 <= z)) (PreH21 : (z < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH24 : ((-1) <= last)) (PreH25 : (last < 26)) (PreH26 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH27 : ((Zlength (next_l)) = 26)) (PreH28 : ((Zlength (prev_l)) = 26)) (PreH29 : ((Zlength (used_l)) = 26)) (PreH30 : ((Zlength (seen_l)) = 26)) (PreH31 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH32 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH33 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH34 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH35 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0) ” 
  &&  “ ((Znth last next_l 0) < 0) ” 
  &&  “ (last >= 0) ” 
  &&  “ (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ (last <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (z <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (last >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (z >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 )) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z i next_l prev_l used_l seen_l last ) ” 
  &&  “ ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0) ” 
  &&  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0) ”
  &&  (((( &( "prev" ) ) + (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) * sizeof(INT)))) # Int  |-> (Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0))
  **  (IntArray.missing_i ( &( "prev" ) ) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) 0 26 prev_l )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
.

Definition solver_partial_solve_wit_13 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0)) (PreH2 : ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : ((Znth last next_l 0) >= 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l)) = 26)) (PreH29 : ((Zlength (prev_l)) = 26)) (PreH30 : ((Zlength (used_l)) = 26)) (PreH31 : ((Zlength (seen_l)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0) ” 
  &&  “ ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ ((Znth last next_l 0) >= 0) ” 
  &&  “ (last >= 0) ” 
  &&  “ (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ (last <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (z <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (last >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (z >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 )) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z i next_l prev_l used_l seen_l last ) ” 
  &&  “ ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0) ” 
  &&  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0) ”
  &&  (((( &( "prev" ) ) + (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) * sizeof(INT)))) # Int  |-> (Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0))
  **  (IntArray.missing_i ( &( "prev" ) ) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) 0 26 prev_l )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
.

Definition solver_partial_solve_wit_14 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0)) (PreH3 : ((Znth last next_l 0) < 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l)) = 26)) (PreH29 : ((Zlength (prev_l)) = 26)) (PreH30 : ((Zlength (used_l)) = 26)) (PreH31 : ((Zlength (seen_l)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) = last) ” 
  &&  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0) ” 
  &&  “ ((Znth last next_l 0) < 0) ” 
  &&  “ (last >= 0) ” 
  &&  “ (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ (last <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (z <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (last >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (z >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 )) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z i next_l prev_l used_l seen_l last ) ” 
  &&  “ ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0) ” 
  &&  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0) ”
  &&  (((( &( "next" ) ) + (last * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "next" ) ) last 0 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
.

Definition solver_partial_solve_wit_15 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0)) (PreH3 : ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH4 : ((Znth last next_l 0) >= 0)) (PreH5 : (last >= 0)) (PreH6 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH7 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH8 : (last <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (z <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (last >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (z >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH17 : (n_pre = (Zlength (g)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (rows)) = n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH22 : (0 <= z)) (PreH23 : (z < n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH26 : ((-1) <= last)) (PreH27 : (last < 26)) (PreH28 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH29 : ((Zlength (next_l)) = 26)) (PreH30 : ((Zlength (prev_l)) = 26)) (PreH31 : ((Zlength (used_l)) = 26)) (PreH32 : ((Zlength (seen_l)) = 26)) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH34 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH35 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH36 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH37 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) = last) ” 
  &&  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0) ” 
  &&  “ ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ ((Znth last next_l 0) >= 0) ” 
  &&  “ (last >= 0) ” 
  &&  “ (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ (last <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (z <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (last >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (z >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 )) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z i next_l prev_l used_l seen_l last ) ” 
  &&  “ ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0) ” 
  &&  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0) ”
  &&  (((( &( "next" ) ) + (last * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "next" ) ) last 0 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
.

Definition solver_partial_solve_wit_16 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) < 0)) (PreH2 : ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : ((Znth last next_l 0) >= 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l)) = 26)) (PreH29 : ((Zlength (prev_l)) = 26)) (PreH30 : ((Zlength (used_l)) = 26)) (PreH31 : ((Zlength (seen_l)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) < 0) ” 
  &&  “ ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ ((Znth last next_l 0) >= 0) ” 
  &&  “ (last >= 0) ” 
  &&  “ (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ (last <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (z <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (last >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (z >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 )) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z i next_l prev_l used_l seen_l last ) ” 
  &&  “ ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0) ” 
  &&  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0) ”
  &&  (((( &( "next" ) ) + (last * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "next" ) ) last 0 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
.

Definition solver_partial_solve_wit_17 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) < 0)) (PreH2 : ((Znth last next_l 0) < 0)) (PreH3 : (last >= 0)) (PreH4 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH6 : (last <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (z <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (last >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (z >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH15 : (n_pre = (Zlength (g)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 100000)) (PreH18 : ((Zlength (rows)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH20 : (0 <= z)) (PreH21 : (z < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH24 : ((-1) <= last)) (PreH25 : (last < 26)) (PreH26 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH27 : ((Zlength (next_l)) = 26)) (PreH28 : ((Zlength (prev_l)) = 26)) (PreH29 : ((Zlength (used_l)) = 26)) (PreH30 : ((Zlength (seen_l)) = 26)) (PreH31 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH32 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH33 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH34 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH35 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) < 0) ” 
  &&  “ ((Znth last next_l 0) < 0) ” 
  &&  “ (last >= 0) ” 
  &&  “ (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ (last <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (z <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (last >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (z >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 )) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z i next_l prev_l used_l seen_l last ) ” 
  &&  “ ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0) ” 
  &&  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0) ”
  &&  (((( &( "next" ) ) + (last * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "next" ) ) last 0 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
.

Definition solver_partial_solve_wit_18 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0)) (PreH3 : ((Znth last next_l 0) < 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l)) = 26)) (PreH29 : ((Zlength (prev_l)) = 26)) (PreH30 : ((Zlength (used_l)) = 26)) (PreH31 : ((Zlength (seen_l)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) = last) ” 
  &&  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0) ” 
  &&  “ ((Znth last next_l 0) < 0) ” 
  &&  “ (last >= 0) ” 
  &&  “ (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ (last <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (z <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (last >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (z >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 )) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z i next_l prev_l used_l seen_l last ) ” 
  &&  “ ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0) ” 
  &&  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0) ”
  &&  (((( &( "prev" ) ) + (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "prev" ) ) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) 0 26 prev_l )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
.

Definition solver_partial_solve_wit_19 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) = last)) (PreH2 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0)) (PreH3 : ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH4 : ((Znth last next_l 0) >= 0)) (PreH5 : (last >= 0)) (PreH6 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH7 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH8 : (last <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (z <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : (last >= INT_MIN)) (PreH13 : (i >= INT_MIN)) (PreH14 : (z >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH17 : (n_pre = (Zlength (g)))) (PreH18 : (1 <= n_pre)) (PreH19 : (n_pre <= 100000)) (PreH20 : ((Zlength (rows)) = n_pre)) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH22 : (0 <= z)) (PreH23 : (z < n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH26 : ((-1) <= last)) (PreH27 : (last < 26)) (PreH28 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH29 : ((Zlength (next_l)) = 26)) (PreH30 : ((Zlength (prev_l)) = 26)) (PreH31 : ((Zlength (used_l)) = 26)) (PreH32 : ((Zlength (seen_l)) = 26)) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH34 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH35 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH36 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH37 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) = last) ” 
  &&  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) >= 0) ” 
  &&  “ ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ ((Znth last next_l 0) >= 0) ” 
  &&  “ (last >= 0) ” 
  &&  “ (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ (last <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (z <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (last >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (z >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 )) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z i next_l prev_l used_l seen_l last ) ” 
  &&  “ ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0) ” 
  &&  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0) ”
  &&  (((( &( "prev" ) ) + (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "prev" ) ) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) 0 26 prev_l )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
.

Definition solver_partial_solve_wit_20 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) < 0)) (PreH2 : ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH3 : ((Znth last next_l 0) >= 0)) (PreH4 : (last >= 0)) (PreH5 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH6 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH7 : (last <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (z <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (last >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (z >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH16 : (n_pre = (Zlength (g)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 100000)) (PreH19 : ((Zlength (rows)) = n_pre)) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH21 : (0 <= z)) (PreH22 : (z < n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH25 : ((-1) <= last)) (PreH26 : (last < 26)) (PreH27 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH28 : ((Zlength (next_l)) = 26)) (PreH29 : ((Zlength (prev_l)) = 26)) (PreH30 : ((Zlength (used_l)) = 26)) (PreH31 : ((Zlength (seen_l)) = 26)) (PreH32 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH34 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH35 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH36 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) < 0) ” 
  &&  “ ((Znth last next_l 0) = ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ ((Znth last next_l 0) >= 0) ” 
  &&  “ (last >= 0) ” 
  &&  “ (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ (last <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (z <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (last >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (z >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 )) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z i next_l prev_l used_l seen_l last ) ” 
  &&  “ ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0) ” 
  &&  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0) ”
  &&  (((( &( "prev" ) ) + (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "prev" ) ) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) 0 26 prev_l )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
.

Definition solver_partial_solve_wit_21 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (seen_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (last: Z) (i: Z) (saved_s: Z) (z: Z) (PreH1 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) < 0)) (PreH2 : ((Znth last next_l 0) < 0)) (PreH3 : (last >= 0)) (PreH4 : (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ))) (PreH5 : (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26)) (PreH6 : (last <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (z <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (last >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (z >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ))) (PreH15 : (n_pre = (Zlength (g)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 100000)) (PreH18 : ((Zlength (rows)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX)))) (PreH20 : (0 <= z)) (PreH21 : (z < n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= (Zlength ((Znth (z) (g) ((@nil Z))))))) (PreH24 : ((-1) <= last)) (PreH25 : (last < 26)) (PreH26 : forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122)))) (PreH27 : ((Zlength (next_l)) = 26)) (PreH28 : ((Zlength (prev_l)) = 26)) (PreH29 : ((Zlength (used_l)) = 26)) (PreH30 : ((Zlength (seen_l)) = 26)) (PreH31 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26)))) (PreH32 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26)))) (PreH33 : (WordScanState g z i next_l prev_l used_l seen_l last )) (PreH34 : ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0)) (PreH35 : ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0)) ,
  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
|--
  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) prev_l 0) < 0) ” 
  &&  “ ((Znth last next_l 0) < 0) ” 
  &&  “ (last >= 0) ” 
  &&  “ (0 <= ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) ” 
  &&  “ (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) < 26) ” 
  &&  “ (last <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (z <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (last >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (z >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (0 <= ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 )) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((((0 < (Zlength ((Znth (k) (g) ((@nil Z)))))) /\ ((Zlength ((Znth (k) (g) ((@nil Z))))) <= 100000)) /\ ((Znth (k) (rows) ((@nil Z))) = (c_string ((Znth (k) (g) ((@nil Z))))))) /\ (valid_string (Znth (k) (g) ((@nil Z))) )) /\ ((string_length ((Znth (k) (g) ((@nil Z))))) < INT_MAX))) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength ((Znth (z) (g) ((@nil Z)))))) ” 
  &&  “ ((-1) <= last) ” 
  &&  “ (last < 26) ” 
  &&  “ forall (k_2: Z) , forall (q: Z) , (((((0 <= k_2) /\ (k_2 < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k_2) (g) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k_2) (g) ((@nil Z)))) (0)) <= 122))) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (seen_l)) = 26) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 26)) -> (((-1) <= (Znth (k_3) (next_l) ((-1)))) /\ ((Znth (k_3) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 26)) -> (((-1) <= (Znth (k_4) (prev_l) ((-1)))) /\ ((Znth (k_4) (prev_l) ((-1))) < 26))) ” 
  &&  “ (WordScanState g z i next_l prev_l used_l seen_l last ) ” 
  &&  “ ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) <> 0) ” 
  &&  “ ((Znth ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) seen_l 0) = 0) ”
  &&  (((( &( "prev" ) ) + (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "prev" ) ) ((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 ) 0 26 prev_l )
  **  (IntArray.full ( &( "next" ) ) 26 (replace_Znth (last) (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (next_l)) )
  **  (IntArray.full ( &( "seen" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (seen_l)) )
  **  (IntArray.full ( &( "used" ) ) 26 (replace_Znth (((Znth i (c_string ((Znth (z) (g) ((@nil Z))))) 0) - 97 )) (1) (used_l)) )
  **  (CharArray.full saved_s ((Zlength ((Znth (z) (g) ((@nil Z))))) + 1 ) (c_string ((Znth (z) (g) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre z saved_s rows )
  **  (((words_pre + (z * sizeof(PTR)))) # Ptr  |-> saved_s)
  **  (CharArray.undef_full out_pre 64 )
.

Definition solver_partial_solve_wit_22 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (start: Z) (PreH1 : (start < 26)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= start)) (PreH7 : (start <= 26)) (PreH8 : (0 <= len)) (PreH9 : (len <= 26)) (PreH10 : ((Zlength (output_l)) = len)) (PreH11 : ((Zlength (next_l)) = 26)) (PreH12 : ((Zlength (prev_l)) = 26)) (PreH13 : ((Zlength (used_l)) = 26)) (PreH14 : ((Zlength (visited_l)) = 26)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH17 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH18 : (TraversalState next_l prev_l used_l start visited_l output_l )) ,
  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ (start < 26) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= 26) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 26) ” 
  &&  “ ((Zlength (output_l)) = len) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (visited_l)) = 26) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g n_pre next_l prev_l used_l ) ” 
  &&  “ (TraversalState next_l prev_l used_l start visited_l output_l ) ”
  &&  (((( &( "used" ) ) + (start * sizeof(INT)))) # Int  |-> (Znth start used_l 0))
  **  (IntArray.missing_i ( &( "used" ) ) start 0 26 used_l )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
.

Definition solver_partial_solve_wit_23 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (start: Z) (PreH1 : ((Znth start used_l 0) <> 0)) (PreH2 : (start < 26)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start <= 26)) (PreH9 : (0 <= len)) (PreH10 : (len <= 26)) (PreH11 : ((Zlength (output_l)) = len)) (PreH12 : ((Zlength (next_l)) = 26)) (PreH13 : ((Zlength (prev_l)) = 26)) (PreH14 : ((Zlength (used_l)) = 26)) (PreH15 : ((Zlength (visited_l)) = 26)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH18 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH19 : (TraversalState next_l prev_l used_l start visited_l output_l )) ,
  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ ((Znth start used_l 0) <> 0) ” 
  &&  “ (start < 26) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= 26) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 26) ” 
  &&  “ ((Zlength (output_l)) = len) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (visited_l)) = 26) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g n_pre next_l prev_l used_l ) ” 
  &&  “ (TraversalState next_l prev_l used_l start visited_l output_l ) ”
  &&  (((( &( "prev" ) ) + (start * sizeof(INT)))) # Int  |-> (Znth start prev_l 0))
  **  (IntArray.missing_i ( &( "prev" ) ) start 0 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
.

Definition solver_partial_solve_wit_24 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : (c >= 0)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= start)) (PreH7 : (start < 26)) (PreH8 : ((-1) <= c)) (PreH9 : (c < 26)) (PreH10 : (0 <= len)) (PreH11 : (len <= 26)) (PreH12 : ((Zlength (output_l)) = len)) (PreH13 : ((Zlength (next_l)) = 26)) (PreH14 : ((Zlength (prev_l)) = 26)) (PreH15 : ((Zlength (used_l)) = 26)) (PreH16 : ((Zlength (visited_l)) = 26)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH19 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH20 : (PathScanState next_l prev_l used_l start c visited_l output_l )) ,
  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ (c >= 0) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < 26) ” 
  &&  “ ((-1) <= c) ” 
  &&  “ (c < 26) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 26) ” 
  &&  “ ((Zlength (output_l)) = len) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (visited_l)) = 26) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g n_pre next_l prev_l used_l ) ” 
  &&  “ (PathScanState next_l prev_l used_l start c visited_l output_l ) ”
  &&  (((( &( "visited" ) ) + (c * sizeof(INT)))) # Int  |-> (Znth c visited_l 0))
  **  (IntArray.missing_i ( &( "visited" ) ) c 0 26 visited_l )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
.

Definition solver_partial_solve_wit_25 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : ((Znth c visited_l 0) = 0)) (PreH2 : (c >= 0)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start < 26)) (PreH9 : ((-1) <= c)) (PreH10 : (c < 26)) (PreH11 : (0 <= len)) (PreH12 : (len <= 26)) (PreH13 : ((Zlength (output_l)) = len)) (PreH14 : ((Zlength (next_l)) = 26)) (PreH15 : ((Zlength (prev_l)) = 26)) (PreH16 : ((Zlength (used_l)) = 26)) (PreH17 : ((Zlength (visited_l)) = 26)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH20 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH21 : (PathScanState next_l prev_l used_l start c visited_l output_l )) ,
  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ ((Znth c visited_l 0) = 0) ” 
  &&  “ (c >= 0) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < 26) ” 
  &&  “ ((-1) <= c) ” 
  &&  “ (c < 26) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 26) ” 
  &&  “ ((Zlength (output_l)) = len) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (visited_l)) = 26) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g n_pre next_l prev_l used_l ) ” 
  &&  “ (PathScanState next_l prev_l used_l start c visited_l output_l ) ”
  &&  (((( &( "visited" ) ) + (c * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "visited" ) ) c 0 26 visited_l )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
.

Definition solver_partial_solve_wit_26 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : ((Znth c visited_l 0) = 0)) (PreH2 : (c >= 0)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start < 26)) (PreH9 : ((-1) <= c)) (PreH10 : (c < 26)) (PreH11 : (0 <= len)) (PreH12 : (len <= 26)) (PreH13 : ((Zlength (output_l)) = len)) (PreH14 : ((Zlength (next_l)) = 26)) (PreH15 : ((Zlength (prev_l)) = 26)) (PreH16 : ((Zlength (used_l)) = 26)) (PreH17 : ((Zlength (visited_l)) = 26)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH20 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH21 : (PathScanState next_l prev_l used_l start c visited_l output_l )) ,
  (IntArray.full ( &( "visited" ) ) 26 (replace_Znth (c) (1) (visited_l)) )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ ((Znth c visited_l 0) = 0) ” 
  &&  “ (c >= 0) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < 26) ” 
  &&  “ ((-1) <= c) ” 
  &&  “ (c < 26) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 26) ” 
  &&  “ ((Zlength (output_l)) = len) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (visited_l)) = 26) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g n_pre next_l prev_l used_l ) ” 
  &&  “ (PathScanState next_l prev_l used_l start c visited_l output_l ) ”
  &&  (((out_pre + (len * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre len len 64 )
  **  (IntArray.full ( &( "visited" ) ) 26 (replace_Znth (c) (1) (visited_l)) )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (CharArray.seg out_pre 0 len output_l )
.

Definition solver_partial_solve_wit_27 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (c: Z) (start: Z) (PreH1 : ((Znth c visited_l 0) = 0)) (PreH2 : (c >= 0)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= start)) (PreH8 : (start < 26)) (PreH9 : ((-1) <= c)) (PreH10 : (c < 26)) (PreH11 : (0 <= len)) (PreH12 : (len <= 26)) (PreH13 : ((Zlength (output_l)) = len)) (PreH14 : ((Zlength (next_l)) = 26)) (PreH15 : ((Zlength (prev_l)) = 26)) (PreH16 : ((Zlength (used_l)) = 26)) (PreH17 : ((Zlength (visited_l)) = 26)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH20 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH21 : (PathScanState next_l prev_l used_l start c visited_l output_l )) ,
  (CharArray.seg out_pre 0 (len + 1 ) (app (output_l) ((cons ((97 + c )) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (len + 1 ) 64 )
  **  (IntArray.full ( &( "visited" ) ) 26 (replace_Znth (c) (1) (visited_l)) )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
|--
  “ ((Znth c visited_l 0) = 0) ” 
  &&  “ (c >= 0) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < 26) ” 
  &&  “ ((-1) <= c) ” 
  &&  “ (c < 26) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 26) ” 
  &&  “ ((Zlength (output_l)) = len) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (visited_l)) = 26) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g n_pre next_l prev_l used_l ) ” 
  &&  “ (PathScanState next_l prev_l used_l start c visited_l output_l ) ”
  &&  (((( &( "next" ) ) + (c * sizeof(INT)))) # Int  |-> (Znth c next_l 0))
  **  (IntArray.missing_i ( &( "next" ) ) c 0 26 next_l )
  **  (CharArray.seg out_pre 0 (len + 1 ) (app (output_l) ((cons ((97 + c )) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (len + 1 ) 64 )
  **  (IntArray.full ( &( "visited" ) ) 26 (replace_Znth (c) (1) (visited_l)) )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
.

Definition solver_partial_solve_wit_28 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (c: Z) (PreH1 : (c < 26)) (PreH2 : (n_pre = (Zlength (g)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c <= 26)) (PreH8 : (0 <= len)) (PreH9 : (len <= 26)) (PreH10 : ((Zlength (output_l)) = len)) (PreH11 : ((Zlength (next_l)) = 26)) (PreH12 : ((Zlength (prev_l)) = 26)) (PreH13 : ((Zlength (used_l)) = 26)) (PreH14 : ((Zlength (visited_l)) = 26)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH17 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH18 : (TraversalState next_l prev_l used_l 26 visited_l output_l )) (PreH19 : (CoverageScanState used_l visited_l c )) ,
  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ (c < 26) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= 26) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 26) ” 
  &&  “ ((Zlength (output_l)) = len) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (visited_l)) = 26) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g n_pre next_l prev_l used_l ) ” 
  &&  “ (TraversalState next_l prev_l used_l 26 visited_l output_l ) ” 
  &&  “ (CoverageScanState used_l visited_l c ) ”
  &&  (((( &( "used" ) ) + (c * sizeof(INT)))) # Int  |-> (Znth c used_l 0))
  **  (IntArray.missing_i ( &( "used" ) ) c 0 26 used_l )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
.

Definition solver_partial_solve_wit_29 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (visited_l: (@list Z)) (used_l: (@list Z)) (prev_l: (@list Z)) (next_l: (@list Z)) (output_l: (@list Z)) (len: Z) (c: Z) (PreH1 : ((Znth c used_l 0) <> 0)) (PreH2 : (c < 26)) (PreH3 : (n_pre = (Zlength (g)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c <= 26)) (PreH9 : (0 <= len)) (PreH10 : (len <= 26)) (PreH11 : ((Zlength (output_l)) = len)) (PreH12 : ((Zlength (next_l)) = 26)) (PreH13 : ((Zlength (prev_l)) = 26)) (PreH14 : ((Zlength (used_l)) = 26)) (PreH15 : ((Zlength (visited_l)) = 26)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26)))) (PreH18 : (GraphBuildState g n_pre next_l prev_l used_l )) (PreH19 : (TraversalState next_l prev_l used_l 26 visited_l output_l )) (PreH20 : (CoverageScanState used_l visited_l c )) ,
  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ ((Znth c used_l 0) <> 0) ” 
  &&  “ (c < 26) ” 
  &&  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c <= 26) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 26) ” 
  &&  “ ((Zlength (output_l)) = len) ” 
  &&  “ ((Zlength (next_l)) = 26) ” 
  &&  “ ((Zlength (prev_l)) = 26) ” 
  &&  “ ((Zlength (used_l)) = 26) ” 
  &&  “ ((Zlength (visited_l)) = 26) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 26)) -> (((-1) <= (Znth (k) (next_l) ((-1)))) /\ ((Znth (k) (next_l) ((-1))) < 26))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 26)) -> (((-1) <= (Znth (k_2) (prev_l) ((-1)))) /\ ((Znth (k_2) (prev_l) ((-1))) < 26))) ” 
  &&  “ (GraphBuildState g n_pre next_l prev_l used_l ) ” 
  &&  “ (TraversalState next_l prev_l used_l 26 visited_l output_l ) ” 
  &&  “ (CoverageScanState used_l visited_l c ) ”
  &&  (((( &( "visited" ) ) + (c * sizeof(INT)))) # Int  |-> (Znth c visited_l 0))
  **  (IntArray.missing_i ( &( "visited" ) ) c 0 26 visited_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
.

Definition solver_partial_solve_wit_30 := 
forall (out_pre: Z) (words_pre: Z) (n_pre: Z) (rows: (@list (@list Z))) (g: (@list (@list Z))) (next_l: (@list Z)) (prev_l: (@list Z)) (used_l: (@list Z)) (visited_l: (@list Z)) (output_l: (@list Z)) (len: Z) (PreH1 : (n_pre = (Zlength (g)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (rows)) = n_pre)) (PreH5 : (0 <= len)) (PreH6 : (len <= 26)) (PreH7 : ((Zlength (output_l)) = len)) (PreH8 : (SuccessfulTraversal g next_l prev_l used_l visited_l output_l )) ,
  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
  **  (CharArray.undef_seg out_pre len 64 )
|--
  “ (n_pre = (Zlength (g))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (rows)) = n_pre) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 26) ” 
  &&  “ ((Zlength (output_l)) = len) ” 
  &&  “ (SuccessfulTraversal g next_l prev_l used_l visited_l output_l ) ”
  &&  (((out_pre + (len * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre len len 64 )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full ( &( "next" ) ) 26 next_l )
  **  (IntArray.full ( &( "prev" ) ) 26 prev_l )
  **  (IntArray.full ( &( "used" ) ) 26 used_l )
  **  (IntArray.full ( &( "visited" ) ) 26 visited_l )
  **  (CharArray.seg out_pre 0 len output_l )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.
Include ptr_array2_Strategy_Correct.

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
Axiom proof_of_solver_safety_wit_22 : solver_safety_wit_22.
Axiom proof_of_solver_safety_wit_23 : solver_safety_wit_23.
Axiom proof_of_solver_safety_wit_24 : solver_safety_wit_24.
Axiom proof_of_solver_safety_wit_25 : solver_safety_wit_25.
Axiom proof_of_solver_safety_wit_26 : solver_safety_wit_26.
Axiom proof_of_solver_safety_wit_27 : solver_safety_wit_27.
Axiom proof_of_solver_safety_wit_28 : solver_safety_wit_28.
Axiom proof_of_solver_safety_wit_29 : solver_safety_wit_29.
Axiom proof_of_solver_safety_wit_30 : solver_safety_wit_30.
Axiom proof_of_solver_safety_wit_31 : solver_safety_wit_31.
Axiom proof_of_solver_safety_wit_32 : solver_safety_wit_32.
Axiom proof_of_solver_safety_wit_33 : solver_safety_wit_33.
Axiom proof_of_solver_safety_wit_34 : solver_safety_wit_34.
Axiom proof_of_solver_safety_wit_35 : solver_safety_wit_35.
Axiom proof_of_solver_safety_wit_36 : solver_safety_wit_36.
Axiom proof_of_solver_safety_wit_37 : solver_safety_wit_37.
Axiom proof_of_solver_safety_wit_38 : solver_safety_wit_38.
Axiom proof_of_solver_safety_wit_39 : solver_safety_wit_39.
Axiom proof_of_solver_safety_wit_40 : solver_safety_wit_40.
Axiom proof_of_solver_safety_wit_41 : solver_safety_wit_41.
Axiom proof_of_solver_safety_wit_42 : solver_safety_wit_42.
Axiom proof_of_solver_safety_wit_43 : solver_safety_wit_43.
Axiom proof_of_solver_safety_wit_44 : solver_safety_wit_44.
Axiom proof_of_solver_safety_wit_45 : solver_safety_wit_45.
Axiom proof_of_solver_safety_wit_46 : solver_safety_wit_46.
Axiom proof_of_solver_safety_wit_47 : solver_safety_wit_47.
Axiom proof_of_solver_safety_wit_48 : solver_safety_wit_48.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Axiom proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Axiom proof_of_solver_entail_wit_7_3 : solver_entail_wit_7_3.
Axiom proof_of_solver_entail_wit_7_4 : solver_entail_wit_7_4.
Axiom proof_of_solver_entail_wit_7_5 : solver_entail_wit_7_5.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Axiom proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Axiom proof_of_solver_entail_wit_13_1 : solver_entail_wit_13_1.
Axiom proof_of_solver_entail_wit_13_2 : solver_entail_wit_13_2.
Axiom proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Axiom proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Axiom proof_of_solver_entail_wit_14_3 : solver_entail_wit_14_3.
Axiom proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Axiom proof_of_solver_entail_wit_16 : solver_entail_wit_16.
Axiom proof_of_solver_entail_wit_17_1 : solver_entail_wit_17_1.
Axiom proof_of_solver_entail_wit_17_2 : solver_entail_wit_17_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_return_wit_4 : solver_return_wit_4.
Axiom proof_of_solver_return_wit_5 : solver_return_wit_5.
Axiom proof_of_solver_return_wit_6 : solver_return_wit_6.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.
Axiom proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13.
Axiom proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14.
Axiom proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15.
Axiom proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16.
Axiom proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17.
Axiom proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18.
Axiom proof_of_solver_partial_solve_wit_19 : solver_partial_solve_wit_19.
Axiom proof_of_solver_partial_solve_wit_20 : solver_partial_solve_wit_20.
Axiom proof_of_solver_partial_solve_wit_21 : solver_partial_solve_wit_21.
Axiom proof_of_solver_partial_solve_wit_22 : solver_partial_solve_wit_22.
Axiom proof_of_solver_partial_solve_wit_23 : solver_partial_solve_wit_23.
Axiom proof_of_solver_partial_solve_wit_24 : solver_partial_solve_wit_24.
Axiom proof_of_solver_partial_solve_wit_25 : solver_partial_solve_wit_25.
Axiom proof_of_solver_partial_solve_wit_26 : solver_partial_solve_wit_26.
Axiom proof_of_solver_partial_solve_wit_27 : solver_partial_solve_wit_27.
Axiom proof_of_solver_partial_solve_wit_28 : solver_partial_solve_wit_28.
Axiom proof_of_solver_partial_solve_wit_29 : solver_partial_solve_wit_29.
Axiom proof_of_solver_partial_solve_wit_30 : solver_partial_solve_wit_30.

End VC_Correct.
