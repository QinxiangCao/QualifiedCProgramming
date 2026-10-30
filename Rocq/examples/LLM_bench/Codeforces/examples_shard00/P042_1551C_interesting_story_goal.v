From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P042_1551C_interesting_story_lib.
Local Open Scope sac.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.

(*----- Function cmp_desc -----*)

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) __default__List_Z (PreH1 : (1 <= (Zlength (words_data)))) (PreH2 : ((Zlength (words_data)) <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (words_data)))) -> (0 < (Zlength ((Znth i words_data __default__List_Z)))))) (PreH4 : forall (i_2: Z), forall (j: Z), (((((0 <= i_2) /\ (i_2 < (Zlength (words_data)))) /\ (0 <= j)) /\ (j < (Zlength ((Znth i_2 words_data __default__List_Z))))) -> ((97 <= (Znth (j) ((Znth (i_2) (words_data) ((@nil Z)))) (0))) /\ ((Znth (j) ((Znth (i_2) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < n_pre)) -> ((((Znth (i_3) (rows) ((@nil Z))) = (c_string ((Znth (i_3) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (i_3) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (i_3) (words_data) ((@nil Z))))) < INT_MAX)))),
  ((( &( "score" ) )) # Ptr  |->_)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharPtrArray2.full words_pre n_pre rows )
|--
  “ ((5 * n_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (5 * n_pre )) ”
.

Definition solver_safety_wit_2 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) __default__List_Z (PreH1 : (1 <= (Zlength (words_data)))) (PreH2 : ((Zlength (words_data)) <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (words_data)))) -> (0 < (Zlength ((Znth i words_data __default__List_Z)))))) (PreH4 : forall (i_2: Z), forall (j: Z), (((((0 <= i_2) /\ (i_2 < (Zlength (words_data)))) /\ (0 <= j)) /\ (j < (Zlength ((Znth i_2 words_data __default__List_Z))))) -> ((97 <= (Znth (j) ((Znth (i_2) (words_data) ((@nil Z)))) (0))) /\ ((Znth (j) ((Znth (i_2) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < n_pre)) -> ((((Znth (i_3) (rows) ((@nil Z))) = (c_string ((Znth (i_3) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (i_3) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (i_3) (words_data) ((@nil Z))))) < INT_MAX)))),
  ((( &( "score" ) )) # Ptr  |->_)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharPtrArray2.full words_pre n_pre rows )
|--
  “ (5 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 5) ”
.

Definition solver_safety_wit_3 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (retval: Z) __default__List_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= (Zlength (words_data)))) (PreH3 : ((Zlength (words_data)) <= 200000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (words_data)))) -> (0 < (Zlength ((Znth i words_data __default__List_Z)))))) (PreH5 : forall (i_2: Z), forall (j: Z), (((((0 <= i_2) /\ (i_2 < (Zlength (words_data)))) /\ (0 <= j)) /\ (j < (Zlength ((Znth i_2 words_data __default__List_Z))))) -> ((97 <= (Znth (j) ((Znth (i_2) (words_data) ((@nil Z)))) (0))) /\ ((Znth (j) ((Znth (i_2) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH6 : ((TotalLength (words_data)) <= 200000)) (PreH7 : (n_pre = (Zlength (words_data)))) (PreH8 : ((Zlength (rows)) = n_pre)) (PreH9 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < n_pre)) -> ((((Znth (i_3) (rows) ((@nil Z))) = (c_string ((Znth (i_3) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (i_3) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (i_3) (words_data) ((@nil Z))))) < INT_MAX)))),
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_full retval (5 * n_pre ) )
  **  ((( &( "score" ) )) # Ptr  |-> retval)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharPtrArray2.full words_pre n_pre rows )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score_mem: (@list (@option Z))) (row_ptr: Z) (i: Z) (score: Z) (retval: Z) (PreH1 : (retval = (string_length ((Znth (i) (words_data) ((@nil Z))))))) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH12 : (ScoreBuildState words_data i score_mem )),
  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.full ( &( "cnt" ) ) 5 (repeat_Z (0) (5)) )
  **  (store_string row_ptr (Znth (i) (words_data) ((@nil Z))) )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ))) (PreH2 : (((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ) < 5)) (PreH3 : (len <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (len >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j < len)) (PreH8 : (n_pre = (Zlength (words_data)))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((TotalLength (words_data)) <= 200000)) (PreH12 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH18 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH19 : (0 <= j)) (PreH20 : (j <= len)) (PreH21 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH22 : ((Zlength (cnt_data)) = 5)) (PreH23 : (ScoreBuildState words_data i score_mem )) (PreH24 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data )),
  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
|--
  “ (((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 )) ”
.

Definition solver_safety_wit_6 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ))) (PreH2 : (((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ) < 5)) (PreH3 : (len <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (len >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j < len)) (PreH8 : (n_pre = (Zlength (words_data)))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((TotalLength (words_data)) <= 200000)) (PreH12 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH18 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH19 : (0 <= j)) (PreH20 : (j <= len)) (PreH21 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH22 : ((Zlength (cnt_data)) = 5)) (PreH23 : (ScoreBuildState words_data i score_mem )) (PreH24 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data )),
  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
|--
  “ (97 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solver_safety_wit_7 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ))) (PreH2 : (((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ) < 5)) (PreH3 : (len <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (len >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j < len)) (PreH8 : (n_pre = (Zlength (words_data)))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((TotalLength (words_data)) <= 200000)) (PreH12 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH18 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH19 : (0 <= j)) (PreH20 : (j <= len)) (PreH21 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH22 : ((Zlength (cnt_data)) = 5)) (PreH23 : (ScoreBuildState words_data i score_mem )) (PreH24 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data )),
  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ (((Znth ((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 ) cnt_data 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth ((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 ) cnt_data 0) + 1 )) ”
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ))) (PreH2 : (((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ) < 5)) (PreH3 : (len <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (len >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j < len)) (PreH8 : (n_pre = (Zlength (words_data)))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((TotalLength (words_data)) <= 200000)) (PreH12 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH18 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH19 : (0 <= j)) (PreH20 : (j <= len)) (PreH21 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH22 : ((Zlength (cnt_data)) = 5)) (PreH23 : (ScoreBuildState words_data i score_mem )) (PreH24 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data )),
  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ (((Znth ((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 ) cnt_data 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth ((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 ) cnt_data 0) + 1 )) ”
).

Definition solver_safety_wit_7_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ))) (PreH2 : (((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ) < 5)) (PreH3 : (len <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (len >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j < len)) (PreH8 : (n_pre = (Zlength (words_data)))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((TotalLength (words_data)) <= 200000)) (PreH12 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH18 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH19 : (0 <= j)) (PreH20 : (j <= len)) (PreH21 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH22 : ((Zlength (cnt_data)) = 5)) (PreH23 : (ScoreBuildState words_data i score_mem )) (PreH24 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data )),
  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ (((Znth ((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 ) cnt_data 0) + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_7_split_goal_2 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ))) (PreH2 : (((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ) < 5)) (PreH3 : (len <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (len >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j < len)) (PreH8 : (n_pre = (Zlength (words_data)))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((TotalLength (words_data)) <= 200000)) (PreH12 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH18 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH19 : (0 <= j)) (PreH20 : (j <= len)) (PreH21 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH22 : ((Zlength (cnt_data)) = 5)) (PreH23 : (ScoreBuildState words_data i score_mem )) (PreH24 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data )),
  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ ((INT_MIN) <= ((Znth ((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 ) cnt_data 0) + 1 )) ”
.

Definition solver_safety_wit_8 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ))) (PreH2 : (((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ) < 5)) (PreH3 : (len <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (len >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j < len)) (PreH8 : (n_pre = (Zlength (words_data)))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((TotalLength (words_data)) <= 200000)) (PreH12 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH18 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH19 : (0 <= j)) (PreH20 : (j <= len)) (PreH21 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH22 : ((Zlength (cnt_data)) = 5)) (PreH23 : (ScoreBuildState words_data i score_mem )) (PreH24 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data )),
  (IntArray.full ( &( "cnt" ) ) 5 (replace_Znth (((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 ) cnt_data 0) + 1 )) (cnt_data)) )
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_9 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (j >= len)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH13 : (0 <= j)) (PreH14 : (j <= len)) (PreH15 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH16 : ((Zlength (cnt_data)) = 5)) (PreH17 : (ScoreBuildState words_data i score_mem )) (PreH18 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data )),
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH11 : (0 <= c)) (PreH12 : (c <= 5)) (PreH13 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH14 : ((Zlength (cnt_data)) = 5)) (PreH15 : (ScoreRowState words_data i c score_mem )) (PreH16 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
|--
  “ (5 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 5) ”
.

Definition solver_safety_wit_11 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((c * n_pre ) + i ))) (PreH2 : (((c * n_pre ) + i ) < (5 * n_pre ))) (PreH3 : (len <= INT_MAX)) (PreH4 : (len >= INT_MIN)) (PreH5 : (c < 5)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((TotalLength (words_data)) <= 200000)) (PreH10 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH16 : (0 <= c)) (PreH17 : (c <= 5)) (PreH18 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH19 : ((Zlength (cnt_data)) = 5)) (PreH20 : (ScoreRowState words_data i c score_mem )) (PreH21 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
|--
  “ (((c * n_pre ) + i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((c * n_pre ) + i )) ”
.

Definition solver_safety_wit_12 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((c * n_pre ) + i ))) (PreH2 : (((c * n_pre ) + i ) < (5 * n_pre ))) (PreH3 : (len <= INT_MAX)) (PreH4 : (len >= INT_MIN)) (PreH5 : (c < 5)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((TotalLength (words_data)) <= 200000)) (PreH10 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH16 : (0 <= c)) (PreH17 : (c <= 5)) (PreH18 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH19 : ((Zlength (cnt_data)) = 5)) (PreH20 : (ScoreRowState words_data i c score_mem )) (PreH21 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
|--
  “ ((c * n_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (c * n_pre )) ”
.

Definition solver_safety_wit_13 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((c * n_pre ) + i ))) (PreH2 : (((c * n_pre ) + i ) < (5 * n_pre ))) (PreH3 : (len <= INT_MAX)) (PreH4 : (len >= INT_MIN)) (PreH5 : (c < 5)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((TotalLength (words_data)) <= 200000)) (PreH10 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH16 : (0 <= c)) (PreH17 : (c <= 5)) (PreH18 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH19 : ((Zlength (cnt_data)) = 5)) (PreH20 : (ScoreRowState words_data i c score_mem )) (PreH21 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ (((2 * (Znth c cnt_data 0) ) - len ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((2 * (Znth c cnt_data 0) ) - len )) ”
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((c * n_pre ) + i ))) (PreH2 : (((c * n_pre ) + i ) < (5 * n_pre ))) (PreH3 : (len <= INT_MAX)) (PreH4 : (len >= INT_MIN)) (PreH5 : (c < 5)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((TotalLength (words_data)) <= 200000)) (PreH10 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH16 : (0 <= c)) (PreH17 : (c <= 5)) (PreH18 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH19 : ((Zlength (cnt_data)) = 5)) (PreH20 : (ScoreRowState words_data i c score_mem )) (PreH21 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ (((2 * (Znth c cnt_data 0) ) - len ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((2 * (Znth c cnt_data 0) ) - len )) ”
).

Definition solver_safety_wit_13_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((c * n_pre ) + i ))) (PreH2 : (((c * n_pre ) + i ) < (5 * n_pre ))) (PreH3 : (len <= INT_MAX)) (PreH4 : (len >= INT_MIN)) (PreH5 : (c < 5)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((TotalLength (words_data)) <= 200000)) (PreH10 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH16 : (0 <= c)) (PreH17 : (c <= 5)) (PreH18 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH19 : ((Zlength (cnt_data)) = 5)) (PreH20 : (ScoreRowState words_data i c score_mem )) (PreH21 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ (((2 * (Znth c cnt_data 0) ) - len ) <= INT_MAX) ”
.

Definition solver_safety_wit_13_split_goal_2 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((c * n_pre ) + i ))) (PreH2 : (((c * n_pre ) + i ) < (5 * n_pre ))) (PreH3 : (len <= INT_MAX)) (PreH4 : (len >= INT_MIN)) (PreH5 : (c < 5)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((TotalLength (words_data)) <= 200000)) (PreH10 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH16 : (0 <= c)) (PreH17 : (c <= 5)) (PreH18 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH19 : ((Zlength (cnt_data)) = 5)) (PreH20 : (ScoreRowState words_data i c score_mem )) (PreH21 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ ((INT_MIN) <= ((2 * (Znth c cnt_data 0) ) - len )) ”
.

Definition solver_safety_wit_14 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((c * n_pre ) + i ))) (PreH2 : (((c * n_pre ) + i ) < (5 * n_pre ))) (PreH3 : (len <= INT_MAX)) (PreH4 : (len >= INT_MIN)) (PreH5 : (c < 5)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((TotalLength (words_data)) <= 200000)) (PreH10 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH16 : (0 <= c)) (PreH17 : (c <= 5)) (PreH18 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH19 : ((Zlength (cnt_data)) = 5)) (PreH20 : (ScoreRowState words_data i c score_mem )) (PreH21 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ ((2 * (Znth c cnt_data 0) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (2 * (Znth c cnt_data 0) )) ”
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((c * n_pre ) + i ))) (PreH2 : (((c * n_pre ) + i ) < (5 * n_pre ))) (PreH3 : (len <= INT_MAX)) (PreH4 : (len >= INT_MIN)) (PreH5 : (c < 5)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((TotalLength (words_data)) <= 200000)) (PreH10 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH16 : (0 <= c)) (PreH17 : (c <= 5)) (PreH18 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH19 : ((Zlength (cnt_data)) = 5)) (PreH20 : (ScoreRowState words_data i c score_mem )) (PreH21 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ ((2 * (Znth c cnt_data 0) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (2 * (Znth c cnt_data 0) )) ”
).

Definition solver_safety_wit_14_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((c * n_pre ) + i ))) (PreH2 : (((c * n_pre ) + i ) < (5 * n_pre ))) (PreH3 : (len <= INT_MAX)) (PreH4 : (len >= INT_MIN)) (PreH5 : (c < 5)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((TotalLength (words_data)) <= 200000)) (PreH10 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH16 : (0 <= c)) (PreH17 : (c <= 5)) (PreH18 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH19 : ((Zlength (cnt_data)) = 5)) (PreH20 : (ScoreRowState words_data i c score_mem )) (PreH21 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ ((2 * (Znth c cnt_data 0) ) <= INT_MAX) ”
.

Definition solver_safety_wit_14_split_goal_2 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((c * n_pre ) + i ))) (PreH2 : (((c * n_pre ) + i ) < (5 * n_pre ))) (PreH3 : (len <= INT_MAX)) (PreH4 : (len >= INT_MIN)) (PreH5 : (c < 5)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((TotalLength (words_data)) <= 200000)) (PreH10 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH16 : (0 <= c)) (PreH17 : (c <= 5)) (PreH18 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH19 : ((Zlength (cnt_data)) = 5)) (PreH20 : (ScoreRowState words_data i c score_mem )) (PreH21 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ ((INT_MIN) <= (2 * (Znth c cnt_data 0) )) ”
.

Definition solver_safety_wit_15 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((c * n_pre ) + i ))) (PreH2 : (((c * n_pre ) + i ) < (5 * n_pre ))) (PreH3 : (len <= INT_MAX)) (PreH4 : (len >= INT_MIN)) (PreH5 : (c < 5)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((TotalLength (words_data)) <= 200000)) (PreH10 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH16 : (0 <= c)) (PreH17 : (c <= 5)) (PreH18 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH19 : ((Zlength (cnt_data)) = 5)) (PreH20 : (ScoreRowState words_data i c score_mem )) (PreH21 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_16 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((c * n_pre ) + i ))) (PreH2 : (((c * n_pre ) + i ) < (5 * n_pre ))) (PreH3 : (len <= INT_MAX)) (PreH4 : (len >= INT_MIN)) (PreH5 : (c < 5)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((TotalLength (words_data)) <= 200000)) (PreH10 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH16 : (0 <= c)) (PreH17 : (c <= 5)) (PreH18 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH19 : ((Zlength (cnt_data)) = 5)) (PreH20 : (ScoreRowState words_data i c score_mem )) (PreH21 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  (IntArray.mixed_full score (5 * n_pre ) (replace_Znth (((c * n_pre ) + i )) ((Some (((2 * (Znth c cnt_data 0) ) - len )))) (score_mem)) )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
|--
  “ ((c + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (c + 1 )) ”
.

Definition solver_safety_wit_17 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (c >= 5)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH12 : (0 <= c)) (PreH13 : (c <= 5)) (PreH14 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH15 : ((Zlength (cnt_data)) = 5)) (PreH16 : (ScoreRowState words_data i c score_mem )) (PreH17 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_18 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (scores: (@list Z)) (score: Z) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : ((Zlength (scores)) = (5 * n_pre ))) (PreH7 : (ScoreTable words_data scores )),
  ((( &( "answer" ) )) # Int  |->_)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.full score (5 * n_pre ) scores )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_19 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (scores: (@list Z)) (score: Z) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : ((Zlength (scores)) = (5 * n_pre ))) (PreH7 : (ScoreTable words_data scores )),
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "answer" ) )) # Int  |-> 0)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.full score (5 * n_pre ) scores )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_20 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c <= 5)) (PreH8 : (0 <= answer)) (PreH9 : (answer <= n_pre)) (PreH10 : ((Zlength (scores)) = (5 * n_pre ))) (PreH11 : (PreparedScoreTable words_data c scores )) (PreH12 : (AnswerState words_data c answer )) (PreH13 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))),
  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.full score (5 * n_pre ) scores )
|--
  “ (5 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 5) ”
.

Definition solver_safety_wit_21 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (before: (@list Z)) (block: (@list Z)) (after: (@list Z)) (c: Z) (answer: Z) (score: Z) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c < 5)) (PreH8 : (0 <= answer)) (PreH9 : (answer <= n_pre)) (PreH10 : (PreparedScoreTable words_data c (app (before) ((app (block) (after)))) )) (PreH11 : (AnswerState words_data c answer )) (PreH12 : ((Zlength (before)) = (c * n_pre ))) (PreH13 : ((Zlength (block)) = n_pre)) (PreH14 : ((Zlength (after)) = (((5 - c ) - 1 ) * n_pre ))) (PreH15 : forall (p: Z), (((0 <= p) /\ (p < (Zlength (block)))) -> (((-200000) <= (Znth (p) (block) (0))) /\ ((Znth (p) (block) (0)) <= 200000)))),
  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.seg score 0 (c * n_pre ) before )
  **  (IntArray.full (score + ((c * n_pre ) * sizeof(INT))) n_pre block )
  **  (IntArray.seg score ((c + 1 ) * n_pre ) (5 * n_pre ) after )
|--
  “ ((c * n_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (c * n_pre )) ”
.

Definition solver_safety_wit_22 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (scores: (@list Z)) (c: Z) (answer: Z) (score: Z) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c < 5)) (PreH8 : (0 <= answer)) (PreH9 : (answer <= n_pre)) (PreH10 : ((Zlength (scores)) = (5 * n_pre ))) (PreH11 : (PreparedScoreTable words_data (c + 1 ) scores )) (PreH12 : (AnswerState words_data c answer )) (PreH13 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) )) (PreH14 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))),
  ((( &( "take" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.full score (5 * n_pre ) scores )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_23 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (scores: (@list Z)) (c: Z) (answer: Z) (score: Z) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c < 5)) (PreH8 : (0 <= answer)) (PreH9 : (answer <= n_pre)) (PreH10 : ((Zlength (scores)) = (5 * n_pre ))) (PreH11 : (PreparedScoreTable words_data (c + 1 ) scores )) (PreH12 : (AnswerState words_data c answer )) (PreH13 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) )) (PreH14 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))),
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.full score (5 * n_pre ) scores )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_24 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (sum: Z) (take: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : (take < n_pre)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : ((Zlength (scores)) = (5 * n_pre ))) (PreH12 : (PreparedScoreTable words_data (c + 1 ) scores )) (PreH13 : (AnswerState words_data c answer )) (PreH14 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) )) (PreH15 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))) (PreH16 : (0 <= take)) (PreH17 : (take <= n_pre)) (PreH18 : (0 <= ((c * n_pre ) + take ))) (PreH19 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH20 : (0 <= sum)) (PreH21 : (sum <= 200000)) (PreH22 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum )),
  (IntArray.full score (5 * n_pre ) scores )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "take" ) )) # Int  |-> take)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
|--
  “ ((sum + (Znth ((c * n_pre ) + take ) scores 0) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (sum + (Znth ((c * n_pre ) + take ) scores 0) )) ”
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (sum: Z) (take: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : (take < n_pre)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : ((Zlength (scores)) = (5 * n_pre ))) (PreH12 : (PreparedScoreTable words_data (c + 1 ) scores )) (PreH13 : (AnswerState words_data c answer )) (PreH14 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) )) (PreH15 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))) (PreH16 : (0 <= take)) (PreH17 : (take <= n_pre)) (PreH18 : (0 <= ((c * n_pre ) + take ))) (PreH19 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH20 : (0 <= sum)) (PreH21 : (sum <= 200000)) (PreH22 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum )),
  (IntArray.full score (5 * n_pre ) scores )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "take" ) )) # Int  |-> take)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
|--
  “ ((sum + (Znth ((c * n_pre ) + take ) scores 0) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (sum + (Znth ((c * n_pre ) + take ) scores 0) )) ”
).

Definition solver_safety_wit_24_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (sum: Z) (take: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : (take < n_pre)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : ((Zlength (scores)) = (5 * n_pre ))) (PreH12 : (PreparedScoreTable words_data (c + 1 ) scores )) (PreH13 : (AnswerState words_data c answer )) (PreH14 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) )) (PreH15 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))) (PreH16 : (0 <= take)) (PreH17 : (take <= n_pre)) (PreH18 : (0 <= ((c * n_pre ) + take ))) (PreH19 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH20 : (0 <= sum)) (PreH21 : (sum <= 200000)) (PreH22 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum )),
  (IntArray.full score (5 * n_pre ) scores )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "take" ) )) # Int  |-> take)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
|--
  “ ((sum + (Znth ((c * n_pre ) + take ) scores 0) ) <= INT_MAX) ”
.

Definition solver_safety_wit_24_split_goal_2 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (sum: Z) (take: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : (take < n_pre)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : ((Zlength (scores)) = (5 * n_pre ))) (PreH12 : (PreparedScoreTable words_data (c + 1 ) scores )) (PreH13 : (AnswerState words_data c answer )) (PreH14 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) )) (PreH15 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))) (PreH16 : (0 <= take)) (PreH17 : (take <= n_pre)) (PreH18 : (0 <= ((c * n_pre ) + take ))) (PreH19 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH20 : (0 <= sum)) (PreH21 : (sum <= 200000)) (PreH22 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum )),
  (IntArray.full score (5 * n_pre ) scores )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "take" ) )) # Int  |-> take)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
|--
  “ ((INT_MIN) <= (sum + (Znth ((c * n_pre ) + take ) scores 0) )) ”
.

Definition solver_safety_wit_25 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (sum: Z) (take: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : (take < n_pre)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : ((Zlength (scores)) = (5 * n_pre ))) (PreH12 : (PreparedScoreTable words_data (c + 1 ) scores )) (PreH13 : (AnswerState words_data c answer )) (PreH14 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) )) (PreH15 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))) (PreH16 : (0 <= take)) (PreH17 : (take <= n_pre)) (PreH18 : (0 <= ((c * n_pre ) + take ))) (PreH19 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH20 : (0 <= sum)) (PreH21 : (sum <= 200000)) (PreH22 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum )),
  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "take" ) )) # Int  |-> take)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.full score (5 * n_pre ) scores )
|--
  “ (((c * n_pre ) + take ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((c * n_pre ) + take )) ”
.

Definition solver_safety_wit_26 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (sum: Z) (take: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : (take < n_pre)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : ((Zlength (scores)) = (5 * n_pre ))) (PreH12 : (PreparedScoreTable words_data (c + 1 ) scores )) (PreH13 : (AnswerState words_data c answer )) (PreH14 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) )) (PreH15 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))) (PreH16 : (0 <= take)) (PreH17 : (take <= n_pre)) (PreH18 : (0 <= ((c * n_pre ) + take ))) (PreH19 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH20 : (0 <= sum)) (PreH21 : (sum <= 200000)) (PreH22 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum )),
  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "take" ) )) # Int  |-> take)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.full score (5 * n_pre ) scores )
|--
  “ ((c * n_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (c * n_pre )) ”
.

Definition solver_safety_wit_27 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (sum: Z) (take: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : (take < n_pre)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : ((Zlength (scores)) = (5 * n_pre ))) (PreH12 : (PreparedScoreTable words_data (c + 1 ) scores )) (PreH13 : (AnswerState words_data c answer )) (PreH14 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) )) (PreH15 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))) (PreH16 : (0 <= take)) (PreH17 : (take <= n_pre)) (PreH18 : (0 <= ((c * n_pre ) + take ))) (PreH19 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH20 : (0 <= sum)) (PreH21 : (sum <= 200000)) (PreH22 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum )),
  (IntArray.full score (5 * n_pre ) scores )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "take" ) )) # Int  |-> take)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_28 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (sum: Z) (take: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : ((sum + (Znth ((c * n_pre ) + take ) scores 0) ) > 0)) (PreH2 : (take < n_pre)) (PreH3 : (n_pre = (Zlength (words_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((TotalLength (words_data)) <= 200000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c < 5)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= n_pre)) (PreH12 : ((Zlength (scores)) = (5 * n_pre ))) (PreH13 : (PreparedScoreTable words_data (c + 1 ) scores )) (PreH14 : (AnswerState words_data c answer )) (PreH15 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) )) (PreH16 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))) (PreH17 : (0 <= take)) (PreH18 : (take <= n_pre)) (PreH19 : (0 <= ((c * n_pre ) + take ))) (PreH20 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= 200000)) (PreH23 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum )),
  (IntArray.full score (5 * n_pre ) scores )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "take" ) )) # Int  |-> take)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
|--
  “ ((sum + (Znth ((c * n_pre ) + take ) scores 0) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (sum + (Znth ((c * n_pre ) + take ) scores 0) )) ”
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (sum: Z) (take: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : ((sum + (Znth ((c * n_pre ) + take ) scores 0) ) > 0)) (PreH2 : (take < n_pre)) (PreH3 : (n_pre = (Zlength (words_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((TotalLength (words_data)) <= 200000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c < 5)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= n_pre)) (PreH12 : ((Zlength (scores)) = (5 * n_pre ))) (PreH13 : (PreparedScoreTable words_data (c + 1 ) scores )) (PreH14 : (AnswerState words_data c answer )) (PreH15 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) )) (PreH16 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))) (PreH17 : (0 <= take)) (PreH18 : (take <= n_pre)) (PreH19 : (0 <= ((c * n_pre ) + take ))) (PreH20 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= 200000)) (PreH23 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum )),
  (IntArray.full score (5 * n_pre ) scores )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "take" ) )) # Int  |-> take)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
|--
  “ ((sum + (Znth ((c * n_pre ) + take ) scores 0) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (sum + (Znth ((c * n_pre ) + take ) scores 0) )) ”
).

Definition solver_safety_wit_28_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (sum: Z) (take: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : ((sum + (Znth ((c * n_pre ) + take ) scores 0) ) > 0)) (PreH2 : (take < n_pre)) (PreH3 : (n_pre = (Zlength (words_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((TotalLength (words_data)) <= 200000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c < 5)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= n_pre)) (PreH12 : ((Zlength (scores)) = (5 * n_pre ))) (PreH13 : (PreparedScoreTable words_data (c + 1 ) scores )) (PreH14 : (AnswerState words_data c answer )) (PreH15 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) )) (PreH16 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))) (PreH17 : (0 <= take)) (PreH18 : (take <= n_pre)) (PreH19 : (0 <= ((c * n_pre ) + take ))) (PreH20 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= 200000)) (PreH23 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum )),
  (IntArray.full score (5 * n_pre ) scores )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "take" ) )) # Int  |-> take)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
|--
  “ ((sum + (Znth ((c * n_pre ) + take ) scores 0) ) <= INT_MAX) ”
.

Definition solver_safety_wit_28_split_goal_2 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (sum: Z) (take: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : ((sum + (Znth ((c * n_pre ) + take ) scores 0) ) > 0)) (PreH2 : (take < n_pre)) (PreH3 : (n_pre = (Zlength (words_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((TotalLength (words_data)) <= 200000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c < 5)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= n_pre)) (PreH12 : ((Zlength (scores)) = (5 * n_pre ))) (PreH13 : (PreparedScoreTable words_data (c + 1 ) scores )) (PreH14 : (AnswerState words_data c answer )) (PreH15 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) )) (PreH16 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))) (PreH17 : (0 <= take)) (PreH18 : (take <= n_pre)) (PreH19 : (0 <= ((c * n_pre ) + take ))) (PreH20 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= 200000)) (PreH23 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum )),
  (IntArray.full score (5 * n_pre ) scores )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "take" ) )) # Int  |-> take)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
|--
  “ ((INT_MIN) <= (sum + (Znth ((c * n_pre ) + take ) scores 0) )) ”
.

Definition solver_safety_wit_29 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (sum: Z) (take: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : ((sum + (Znth ((c * n_pre ) + take ) scores 0) ) > 0)) (PreH2 : (take < n_pre)) (PreH3 : (n_pre = (Zlength (words_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((TotalLength (words_data)) <= 200000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c < 5)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= n_pre)) (PreH12 : ((Zlength (scores)) = (5 * n_pre ))) (PreH13 : (PreparedScoreTable words_data (c + 1 ) scores )) (PreH14 : (AnswerState words_data c answer )) (PreH15 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) )) (PreH16 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))) (PreH17 : (0 <= take)) (PreH18 : (take <= n_pre)) (PreH19 : (0 <= ((c * n_pre ) + take ))) (PreH20 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= 200000)) (PreH23 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum )),
  (IntArray.full score (5 * n_pre ) scores )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "take" ) )) # Int  |-> take)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
|--
  “ (((c * n_pre ) + take ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((c * n_pre ) + take )) ”
.

Definition solver_safety_wit_30 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (sum: Z) (take: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : ((sum + (Znth ((c * n_pre ) + take ) scores 0) ) > 0)) (PreH2 : (take < n_pre)) (PreH3 : (n_pre = (Zlength (words_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((TotalLength (words_data)) <= 200000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c < 5)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= n_pre)) (PreH12 : ((Zlength (scores)) = (5 * n_pre ))) (PreH13 : (PreparedScoreTable words_data (c + 1 ) scores )) (PreH14 : (AnswerState words_data c answer )) (PreH15 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) )) (PreH16 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))) (PreH17 : (0 <= take)) (PreH18 : (take <= n_pre)) (PreH19 : (0 <= ((c * n_pre ) + take ))) (PreH20 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= 200000)) (PreH23 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum )),
  (IntArray.full score (5 * n_pre ) scores )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "take" ) )) # Int  |-> take)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
|--
  “ ((c * n_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (c * n_pre )) ”
.

Definition solver_safety_wit_31 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (sum: Z) (take: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : ((sum + (Znth ((c * n_pre ) + take ) scores 0) ) > 0)) (PreH2 : (take < n_pre)) (PreH3 : (n_pre = (Zlength (words_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((TotalLength (words_data)) <= 200000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c < 5)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= n_pre)) (PreH12 : ((Zlength (scores)) = (5 * n_pre ))) (PreH13 : (PreparedScoreTable words_data (c + 1 ) scores )) (PreH14 : (AnswerState words_data c answer )) (PreH15 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) )) (PreH16 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))) (PreH17 : (0 <= take)) (PreH18 : (take <= n_pre)) (PreH19 : (0 <= ((c * n_pre ) + take ))) (PreH20 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= 200000)) (PreH23 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum )),
  (IntArray.full score (5 * n_pre ) scores )
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "take" ) )) # Int  |-> take)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (Znth ((c * n_pre ) + take ) scores 0) ))
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
|--
  “ ((take + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (take + 1 )) ”
.

Definition solver_safety_wit_32 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (scores: (@list Z)) (c: Z) (answer: Z) (take: Z) (sum: Z) (score: Z) (PreH1 : (take > answer)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : (0 <= take)) (PreH12 : (take <= n_pre)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= 200000)) (PreH15 : ((Zlength (scores)) = (5 * n_pre ))) (PreH16 : (PreparedScoreTable words_data (c + 1 ) scores )) (PreH17 : (AnswerState words_data c answer )) (PreH18 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum )) (PreH19 : (LetterBest words_data (97 + c ) take )),
  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> take)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.full score (5 * n_pre ) scores )
|--
  “ ((c + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (c + 1 )) ”
.

Definition solver_safety_wit_33 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (scores: (@list Z)) (c: Z) (answer: Z) (take: Z) (sum: Z) (score: Z) (PreH1 : (take <= answer)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : (0 <= take)) (PreH12 : (take <= n_pre)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= 200000)) (PreH15 : ((Zlength (scores)) = (5 * n_pre ))) (PreH16 : (PreparedScoreTable words_data (c + 1 ) scores )) (PreH17 : (AnswerState words_data c answer )) (PreH18 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum )) (PreH19 : (LetterBest words_data (97 + c ) take )),
  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.full score (5 * n_pre ) scores )
|--
  “ ((c + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (c + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (retval: Z) __default__List_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= (Zlength (words_data)))) (PreH3 : ((Zlength (words_data)) <= 200000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (words_data)))) -> (0 < (Zlength ((Znth i words_data __default__List_Z)))))) (PreH5 : forall (i_2: Z), forall (j: Z), (((((0 <= i_2) /\ (i_2 < (Zlength (words_data)))) /\ (0 <= j)) /\ (j < (Zlength ((Znth i_2 words_data __default__List_Z))))) -> ((97 <= (Znth (j) ((Znth (i_2) (words_data) ((@nil Z)))) (0))) /\ ((Znth (j) ((Znth (i_2) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH6 : ((TotalLength (words_data)) <= 200000)) (PreH7 : (n_pre = (Zlength (words_data)))) (PreH8 : ((Zlength (rows)) = n_pre)) (PreH9 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < n_pre)) -> ((((Znth (i_3) (rows) ((@nil Z))) = (c_string ((Znth (i_3) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (i_3) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (i_3) (words_data) ((@nil Z))))) < INT_MAX)))),
  (IntArray.undef_full retval (5 * n_pre ) )
  **  (CharPtrArray2.full words_pre n_pre rows )
|--
  EX (score_mem: (@list (@option Z))),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((Zlength (score_mem)) = (5 * n_pre )) ”
  &&  “ (ScoreBuildState words_data 0 score_mem ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.mixed_full retval (5 * n_pre ) score_mem )
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (retval: Z) __default__List_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= (Zlength (words_data)))) (PreH3 : ((Zlength (words_data)) <= 200000)) (PreH4 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (words_data)))) -> (0 < (Zlength ((Znth i words_data __default__List_Z)))))) (PreH5 : forall (i_2: Z), forall (j: Z), (((((0 <= i_2) /\ (i_2 < (Zlength (words_data)))) /\ (0 <= j)) /\ (j < (Zlength ((Znth i_2 words_data __default__List_Z))))) -> ((97 <= (Znth (j) ((Znth (i_2) (words_data) ((@nil Z)))) (0))) /\ ((Znth (j) ((Znth (i_2) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH6 : ((TotalLength (words_data)) <= 200000)) (PreH7 : (n_pre = (Zlength (words_data)))) (PreH8 : ((Zlength (rows)) = n_pre)) (PreH9 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < n_pre)) -> ((((Znth (i_3) (rows) ((@nil Z))) = (c_string ((Znth (i_3) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (i_3) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (i_3) (words_data) ((@nil Z))))) < INT_MAX)))),
  (IntArray.undef_full retval (5 * n_pre ) )
|--
  EX (score_mem: (@list (@option Z))),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((Zlength (score_mem)) = (5 * n_pre )) ”
  &&  “ (ScoreBuildState words_data 0 score_mem ) ”
  &&  (IntArray.mixed_full retval (5 * n_pre ) score_mem )
).

Definition solver_entail_wit_2 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (score_mem_2: (@list (@option Z))) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_2: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH12 : (ScoreBuildState words_data i score_mem_2 )),
  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem_2 )
|--
  EX (row_ptr: Z) (score_mem: (@list (@option Z))),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (score_mem)) = (5 * n_pre )) ”
  &&  “ (ScoreBuildState words_data i score_mem ) ”
  &&  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr ((string_length ((Znth (i) (words_data) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (score_mem_2: (@list (@option Z))) (i: Z) (row_ptr_2: Z) __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_2: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH12 : (ScoreBuildState words_data i score_mem_2 )),
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
  &&  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
  &&  (CharArray.full row_ptr_2 ((string_length ((Znth (i) (words_data) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (score_mem_2: (@list (@option Z))) (i: Z) (row_ptr_2: Z) __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_2: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH12 : (ScoreBuildState words_data i score_mem_2 )),
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (score_mem_2: (@list (@option Z))) (i: Z) (row_ptr_2: Z) __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_2: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH12 : (ScoreBuildState words_data i score_mem_2 )),
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
.

Definition solver_entail_wit_2_split_goal_spatial :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (score_mem_2: (@list (@option Z))) (i: Z) (row_ptr_2: Z) __default__List_Z (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_2: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH12 : (ScoreBuildState words_data i score_mem_2 )),
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  (CharArray.full row_ptr_2 ((string_length ((Znth (i) (words_data) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
.

Definition solver_entail_wit_3 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score_mem_2: (@list (@option Z))) (row_ptr_2: Z) (i: Z) (score: Z) (retval: Z) (PreH1 : (retval = (string_length ((Znth (i) (words_data) ((@nil Z))))))) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_3: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_3)) /\ (q_3 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_3) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_3) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH12 : (ScoreBuildState words_data i score_mem_2 )),
  (IntArray.full ( &( "cnt" ) ) 5 (repeat_Z (0) (5)) )
  **  (store_string row_ptr_2 (Znth (i) (words_data) ((@nil Z))) )
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr_2 rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr_2)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem_2 )
|--
  EX (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (retval = (Zlength ((Znth (i) (words_data) ((@nil Z)))))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < retval)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= retval) ”
  &&  “ ((Zlength (score_mem)) = (5 * n_pre )) ”
  &&  “ ((Zlength (cnt_data)) = 5) ”
  &&  “ (ScoreBuildState words_data i score_mem ) ”
  &&  “ (CountPrefixState (Znth (i) (words_data) ((@nil Z))) 0 cnt_data ) ”
  &&  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (retval + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (score_mem_2: (@list (@option Z))) (i: Z) (retval: Z) (PreH1 : (retval = (string_length ((Znth (i) (words_data) ((@nil Z))))))) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_3: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_3)) /\ (q_3 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_3) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_3) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH12 : (ScoreBuildState words_data i score_mem_2 )),
  TT && emp 
|--
  “ (CountPrefixState (Znth (i) (words_data) ((@nil Z))) 0 (repeat_Z (0) (5)) ) ”
  &&  “ ((Zlength ((repeat_Z (0) (5)))) = 5) ”
  &&  “ (0 <= retval) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < (string_length ((Znth (i) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101))) ”
  &&  “ (retval = (Zlength ((Znth (i) (words_data) ((@nil Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (score_mem_2: (@list (@option Z))) (i: Z) (retval: Z) (PreH1 : (retval = (string_length ((Znth (i) (words_data) ((@nil Z))))))) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_3: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_3)) /\ (q_3 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_3) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_3) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH12 : (ScoreBuildState words_data i score_mem_2 )),
  (CountPrefixState (Znth (i) (words_data) ((@nil Z))) 0 (repeat_Z (0) (5)) )
.

Definition solver_entail_wit_3_split_goal_2 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (score_mem_2: (@list (@option Z))) (i: Z) (retval: Z) (PreH1 : (retval = (string_length ((Znth (i) (words_data) ((@nil Z))))))) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_3: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_3)) /\ (q_3 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_3) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_3) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH12 : (ScoreBuildState words_data i score_mem_2 )),
  ((Zlength ((repeat_Z (0) (5)))) = 5)
.

Definition solver_entail_wit_3_split_goal_3 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (score_mem_2: (@list (@option Z))) (i: Z) (retval: Z) (PreH1 : (retval = (string_length ((Znth (i) (words_data) ((@nil Z))))))) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_3: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_3)) /\ (q_3 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_3) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_3) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH12 : (ScoreBuildState words_data i score_mem_2 )),
  (0 <= retval)
.

Definition solver_entail_wit_3_split_goal_4 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (score_mem_2: (@list (@option Z))) (i: Z) (retval: Z) (PreH1 : (retval = (string_length ((Znth (i) (words_data) ((@nil Z))))))) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_3: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_3)) /\ (q_3 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_3) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_3) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH12 : (ScoreBuildState words_data i score_mem_2 )),
  forall (q_2: Z), (((0 <= q_2) /\ (q_2 < (string_length ((Znth (i) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))
.

Definition solver_entail_wit_3_split_goal_5 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (score_mem_2: (@list (@option Z))) (i: Z) (retval: Z) (PreH1 : (retval = (string_length ((Znth (i) (words_data) ((@nil Z))))))) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_3: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_3)) /\ (q_3 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_3) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_3) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH12 : (ScoreBuildState words_data i score_mem_2 )),
  (retval = (Zlength ((Znth (i) (words_data) ((@nil Z))))))
.

Definition solver_entail_wit_4 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (j < len)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH12 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH13 : (0 <= j)) (PreH14 : (j <= len)) (PreH15 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH16 : ((Zlength (cnt_data)) = 5)) (PreH17 : (ScoreBuildState words_data i score_mem )) (PreH18 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data )),
  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
|--
  “ (0 <= ((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 )) ”
  &&  “ (((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ) < 5) ”
  &&  “ (len <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (len >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ (j < len) ”
  &&  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (len = (Zlength ((Znth (i) (words_data) ((@nil Z)))))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= len) ”
  &&  “ ((Zlength (score_mem)) = (5 * n_pre )) ”
  &&  “ ((Zlength (cnt_data)) = 5) ”
  &&  “ (ScoreBuildState words_data i score_mem ) ”
  &&  “ (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (len <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (len >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (j < len)) (PreH10 : (n_pre = (Zlength (words_data)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((TotalLength (words_data)) <= 200000)) (PreH14 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH15 : ((Zlength (rows)) = n_pre)) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH20 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH21 : (0 <= j)) (PreH22 : (j <= len)) (PreH23 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH24 : ((Zlength (cnt_data)) = 5)) (PreH25 : (ScoreBuildState words_data i score_mem )) (PreH26 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data )),
  TT && emp 
|--
  “ (((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ) < 5) ”
  &&  “ (0 <= ((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 )) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (len <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (len >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (j < len)) (PreH10 : (n_pre = (Zlength (words_data)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((TotalLength (words_data)) <= 200000)) (PreH14 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH15 : ((Zlength (rows)) = n_pre)) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH20 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH21 : (0 <= j)) (PreH22 : (j <= len)) (PreH23 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH24 : ((Zlength (cnt_data)) = 5)) (PreH25 : (ScoreBuildState words_data i score_mem )) (PreH26 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data )),
  (((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ) < 5)
.

Definition solver_entail_wit_4_split_goal_2 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (len <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (len >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (j < len)) (PreH10 : (n_pre = (Zlength (words_data)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((TotalLength (words_data)) <= 200000)) (PreH14 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH15 : ((Zlength (rows)) = n_pre)) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH20 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH21 : (0 <= j)) (PreH22 : (j <= len)) (PreH23 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH24 : ((Zlength (cnt_data)) = 5)) (PreH25 : (ScoreBuildState words_data i score_mem )) (PreH26 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data )),
  (0 <= ((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ))
.

Definition solver_entail_wit_5 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr_2: Z) (cnt_data_2: (@list Z)) (score_mem_2: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ))) (PreH2 : (((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ) < 5)) (PreH3 : (len <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (len >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j < len)) (PreH8 : (n_pre = (Zlength (words_data)))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((TotalLength (words_data)) <= 200000)) (PreH12 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH18 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH19 : (0 <= j)) (PreH20 : (j <= len)) (PreH21 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH22 : ((Zlength (cnt_data_2)) = 5)) (PreH23 : (ScoreBuildState words_data i score_mem_2 )) (PreH24 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data_2 )),
  (IntArray.full ( &( "cnt" ) ) 5 (replace_Znth (((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 ) cnt_data_2 0) + 1 )) (cnt_data_2)) )
  **  (CharArray.full row_ptr_2 (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr_2 rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr_2)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem_2 )
|--
  EX (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (len = (Zlength ((Znth (i) (words_data) ((@nil Z)))))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101))) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= len) ”
  &&  “ ((Zlength (score_mem)) = (5 * n_pre )) ”
  &&  “ ((Zlength (cnt_data)) = 5) ”
  &&  “ (ScoreBuildState words_data i score_mem ) ”
  &&  “ (CountPrefixState (Znth (i) (words_data) ((@nil Z))) (j + 1 ) cnt_data ) ”
  &&  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (cnt_data_2: (@list Z)) (score_mem_2: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ))) (PreH2 : (((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ) < 5)) (PreH3 : (len <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (len >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j < len)) (PreH8 : (n_pre = (Zlength (words_data)))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((TotalLength (words_data)) <= 200000)) (PreH12 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH18 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH19 : (0 <= j)) (PreH20 : (j <= len)) (PreH21 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH22 : ((Zlength (cnt_data_2)) = 5)) (PreH23 : (ScoreBuildState words_data i score_mem_2 )) (PreH24 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data_2 )),
  TT && emp 
|--
  “ (CountPrefixState (Znth (i) (words_data) ((@nil Z))) (j + 1 ) (replace_Znth (((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 ) cnt_data_2 0) + 1 )) (cnt_data_2)) ) ”
  &&  “ ((Zlength ((replace_Znth (((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 ) cnt_data_2 0) + 1 )) (cnt_data_2)))) = 5) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (cnt_data_2: (@list Z)) (score_mem_2: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ))) (PreH2 : (((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ) < 5)) (PreH3 : (len <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (len >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j < len)) (PreH8 : (n_pre = (Zlength (words_data)))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((TotalLength (words_data)) <= 200000)) (PreH12 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH18 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH19 : (0 <= j)) (PreH20 : (j <= len)) (PreH21 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH22 : ((Zlength (cnt_data_2)) = 5)) (PreH23 : (ScoreBuildState words_data i score_mem_2 )) (PreH24 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data_2 )),
  (CountPrefixState (Znth (i) (words_data) ((@nil Z))) (j + 1 ) (replace_Znth (((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 ) cnt_data_2 0) + 1 )) (cnt_data_2)) )
.

Definition solver_entail_wit_5_split_goal_2 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (cnt_data_2: (@list Z)) (score_mem_2: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ))) (PreH2 : (((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ) < 5)) (PreH3 : (len <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (len >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j < len)) (PreH8 : (n_pre = (Zlength (words_data)))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((TotalLength (words_data)) <= 200000)) (PreH12 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH18 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH19 : (0 <= j)) (PreH20 : (j <= len)) (PreH21 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH22 : ((Zlength (cnt_data_2)) = 5)) (PreH23 : (ScoreBuildState words_data i score_mem_2 )) (PreH24 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data_2 )),
  ((Zlength ((replace_Znth (((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 ) cnt_data_2 0) + 1 )) (cnt_data_2)))) = 5)
.

Definition solver_entail_wit_6 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr_2: Z) (cnt_data_2: (@list Z)) (score_mem_2: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (j >= len)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_2: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH12 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < len)) -> ((97 <= (Znth (q_3) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_3) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH13 : (0 <= j)) (PreH14 : (j <= len)) (PreH15 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH16 : ((Zlength (cnt_data_2)) = 5)) (PreH17 : (ScoreBuildState words_data i score_mem_2 )) (PreH18 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data_2 )),
  (CharPtrArray2.missing_i words_pre n_pre i row_ptr_2 rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr_2)
  **  (CharArray.full row_ptr_2 (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem_2 )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data_2 )
|--
  EX (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (len = (Zlength ((Znth (i) (words_data) ((@nil Z)))))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 5) ”
  &&  “ ((Zlength (score_mem)) = (5 * n_pre )) ”
  &&  “ ((Zlength (cnt_data)) = 5) ”
  &&  “ (ScoreRowState words_data i 0 score_mem ) ”
  &&  “ (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data ) ”
  &&  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (cnt_data_2: (@list Z)) (score_mem_2: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (j >= len)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_2: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH12 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < len)) -> ((97 <= (Znth (q_3) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_3) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH13 : (0 <= j)) (PreH14 : (j <= len)) (PreH15 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH16 : ((Zlength (cnt_data_2)) = 5)) (PreH17 : (ScoreBuildState words_data i score_mem_2 )) (PreH18 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data_2 )),
  TT && emp 
|--
  “ (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data_2 ) ”
  &&  “ (ScoreRowState words_data i 0 score_mem_2 ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
  &&  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (cnt_data_2: (@list Z)) (score_mem_2: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (j >= len)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_2: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH12 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < len)) -> ((97 <= (Znth (q_3) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_3) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH13 : (0 <= j)) (PreH14 : (j <= len)) (PreH15 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH16 : ((Zlength (cnt_data_2)) = 5)) (PreH17 : (ScoreBuildState words_data i score_mem_2 )) (PreH18 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data_2 )),
  (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data_2 )
.

Definition solver_entail_wit_6_split_goal_2 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (cnt_data_2: (@list Z)) (score_mem_2: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (j >= len)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_2: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH12 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < len)) -> ((97 <= (Znth (q_3) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_3) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH13 : (0 <= j)) (PreH14 : (j <= len)) (PreH15 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH16 : ((Zlength (cnt_data_2)) = 5)) (PreH17 : (ScoreBuildState words_data i score_mem_2 )) (PreH18 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data_2 )),
  (ScoreRowState words_data i 0 score_mem_2 )
.

Definition solver_entail_wit_6_split_goal_3 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (cnt_data_2: (@list Z)) (score_mem_2: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (j >= len)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_2: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH12 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < len)) -> ((97 <= (Znth (q_3) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_3) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH13 : (0 <= j)) (PreH14 : (j <= len)) (PreH15 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH16 : ((Zlength (cnt_data_2)) = 5)) (PreH17 : (ScoreBuildState words_data i score_mem_2 )) (PreH18 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data_2 )),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))
.

Definition solver_entail_wit_6_split_goal_4 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (cnt_data_2: (@list Z)) (score_mem_2: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (j >= len)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_2: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH12 : forall (q_3: Z), (((0 <= q_3) /\ (q_3 < len)) -> ((97 <= (Znth (q_3) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_3) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH13 : (0 <= j)) (PreH14 : (j <= len)) (PreH15 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH16 : ((Zlength (cnt_data_2)) = 5)) (PreH17 : (ScoreBuildState words_data i score_mem_2 )) (PreH18 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data_2 )),
  forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))
.

Definition solver_entail_wit_7 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (c < 5)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH12 : (0 <= c)) (PreH13 : (c <= 5)) (PreH14 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH15 : ((Zlength (cnt_data)) = 5)) (PreH16 : (ScoreRowState words_data i c score_mem )) (PreH17 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
|--
  “ (0 <= ((c * n_pre ) + i )) ”
  &&  “ (((c * n_pre ) + i ) < (5 * n_pre )) ”
  &&  “ (len <= INT_MAX) ”
  &&  “ (len >= INT_MIN) ”
  &&  “ (c < 5) ”
  &&  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (len = (Zlength ((Znth (i) (words_data) ((@nil Z)))))) ”
  &&  “ (0 <= c) ”
  &&  “ (c <= 5) ”
  &&  “ ((Zlength (score_mem)) = (5 * n_pre )) ”
  &&  “ ((Zlength (cnt_data)) = 5) ”
  &&  “ (ScoreRowState words_data i c score_mem ) ”
  &&  “ (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data ) ”
  &&  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (c <= INT_MAX)) (PreH2 : (len <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (c >= INT_MIN)) (PreH6 : (len >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (c < 5)) (PreH10 : (n_pre = (Zlength (words_data)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((TotalLength (words_data)) <= 200000)) (PreH14 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH15 : ((Zlength (rows)) = n_pre)) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH20 : (0 <= c)) (PreH21 : (c <= 5)) (PreH22 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH23 : ((Zlength (cnt_data)) = 5)) (PreH24 : (ScoreRowState words_data i c score_mem )) (PreH25 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  TT && emp 
|--
  “ (((c * n_pre ) + i ) < (5 * n_pre )) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (c <= INT_MAX)) (PreH2 : (len <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (c >= INT_MIN)) (PreH6 : (len >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (c < 5)) (PreH10 : (n_pre = (Zlength (words_data)))) (PreH11 : (1 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((TotalLength (words_data)) <= 200000)) (PreH14 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH15 : ((Zlength (rows)) = n_pre)) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH17 : (0 <= i)) (PreH18 : (i < n_pre)) (PreH19 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH20 : (0 <= c)) (PreH21 : (c <= 5)) (PreH22 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH23 : ((Zlength (cnt_data)) = 5)) (PreH24 : (ScoreRowState words_data i c score_mem )) (PreH25 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  (((c * n_pre ) + i ) < (5 * n_pre ))
.

Definition solver_entail_wit_8 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr_2: Z) (cnt_data_2: (@list Z)) (score_mem_2: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((c * n_pre ) + i ))) (PreH2 : (((c * n_pre ) + i ) < (5 * n_pre ))) (PreH3 : (len <= INT_MAX)) (PreH4 : (len >= INT_MIN)) (PreH5 : (c < 5)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((TotalLength (words_data)) <= 200000)) (PreH10 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH16 : (0 <= c)) (PreH17 : (c <= 5)) (PreH18 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH19 : ((Zlength (cnt_data_2)) = 5)) (PreH20 : (ScoreRowState words_data i c score_mem_2 )) (PreH21 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data_2 )),
  (IntArray.mixed_full score (5 * n_pre ) (replace_Znth (((c * n_pre ) + i )) ((Some (((2 * (Znth c cnt_data_2 0) ) - len )))) (score_mem_2)) )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data_2 )
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr_2 rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr_2)
  **  (CharArray.full row_ptr_2 (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
|--
  EX (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (len = (Zlength ((Znth (i) (words_data) ((@nil Z)))))) ”
  &&  “ (0 <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= 5) ”
  &&  “ ((Zlength (score_mem)) = (5 * n_pre )) ”
  &&  “ ((Zlength (cnt_data)) = 5) ”
  &&  “ (ScoreRowState words_data i (c + 1 ) score_mem ) ”
  &&  “ (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data ) ”
  &&  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (cnt_data_2: (@list Z)) (score_mem_2: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((c * n_pre ) + i ))) (PreH2 : (((c * n_pre ) + i ) < (5 * n_pre ))) (PreH3 : (len <= INT_MAX)) (PreH4 : (len >= INT_MIN)) (PreH5 : (c < 5)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((TotalLength (words_data)) <= 200000)) (PreH10 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH16 : (0 <= c)) (PreH17 : (c <= 5)) (PreH18 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH19 : ((Zlength (cnt_data_2)) = 5)) (PreH20 : (ScoreRowState words_data i c score_mem_2 )) (PreH21 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data_2 )),
  TT && emp 
|--
  “ (ScoreRowState words_data i (c + 1 ) (replace_Znth (((c * n_pre ) + i )) ((Some (((2 * (Znth c cnt_data_2 0) ) - len )))) (score_mem_2)) ) ”
  &&  “ ((Zlength ((replace_Znth (((c * n_pre ) + i )) ((Some (((2 * (Znth c cnt_data_2 0) ) - len )))) (score_mem_2)))) = (5 * n_pre )) ”
  &&  emp
).

Definition solver_entail_wit_8_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (cnt_data_2: (@list Z)) (score_mem_2: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((c * n_pre ) + i ))) (PreH2 : (((c * n_pre ) + i ) < (5 * n_pre ))) (PreH3 : (len <= INT_MAX)) (PreH4 : (len >= INT_MIN)) (PreH5 : (c < 5)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((TotalLength (words_data)) <= 200000)) (PreH10 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH16 : (0 <= c)) (PreH17 : (c <= 5)) (PreH18 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH19 : ((Zlength (cnt_data_2)) = 5)) (PreH20 : (ScoreRowState words_data i c score_mem_2 )) (PreH21 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data_2 )),
  (ScoreRowState words_data i (c + 1 ) (replace_Znth (((c * n_pre ) + i )) ((Some (((2 * (Znth c cnt_data_2 0) ) - len )))) (score_mem_2)) )
.

Definition solver_entail_wit_8_split_goal_2 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (cnt_data_2: (@list Z)) (score_mem_2: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((c * n_pre ) + i ))) (PreH2 : (((c * n_pre ) + i ) < (5 * n_pre ))) (PreH3 : (len <= INT_MAX)) (PreH4 : (len >= INT_MIN)) (PreH5 : (c < 5)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((TotalLength (words_data)) <= 200000)) (PreH10 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH16 : (0 <= c)) (PreH17 : (c <= 5)) (PreH18 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH19 : ((Zlength (cnt_data_2)) = 5)) (PreH20 : (ScoreRowState words_data i c score_mem_2 )) (PreH21 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data_2 )),
  ((Zlength ((replace_Znth (((c * n_pre ) + i )) ((Some (((2 * (Znth c cnt_data_2 0) ) - len )))) (score_mem_2)))) = (5 * n_pre ))
.

Definition solver_entail_wit_9 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem_2: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (c >= 5)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_2: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH12 : (0 <= c)) (PreH13 : (c <= 5)) (PreH14 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH15 : ((Zlength (cnt_data)) = 5)) (PreH16 : (ScoreRowState words_data i c score_mem_2 )) (PreH17 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem_2 )
|--
  EX (score_mem: (@list (@option Z))),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (score_mem)) = (5 * n_pre )) ”
  &&  “ (ScoreBuildState words_data (i + 1 ) score_mem ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem_2: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (c >= 5)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_2: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH12 : (0 <= c)) (PreH13 : (c <= 5)) (PreH14 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH15 : ((Zlength (cnt_data)) = 5)) (PreH16 : (ScoreRowState words_data i c score_mem_2 )) (PreH17 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
|--
  “ (ScoreBuildState words_data (i + 1 ) score_mem_2 ) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
  &&  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
).

Definition solver_entail_wit_9_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem_2: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (c >= 5)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_2: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH12 : (0 <= c)) (PreH13 : (c <= 5)) (PreH14 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH15 : ((Zlength (cnt_data)) = 5)) (PreH16 : (ScoreRowState words_data i c score_mem_2 )) (PreH17 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
|--
  “ (ScoreBuildState words_data (i + 1 ) score_mem_2 ) ”
.

Definition solver_entail_wit_9_split_goal_2 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem_2: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (c >= 5)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_2: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH12 : (0 <= c)) (PreH13 : (c <= 5)) (PreH14 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH15 : ((Zlength (cnt_data)) = 5)) (PreH16 : (ScoreRowState words_data i c score_mem_2 )) (PreH17 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
.

Definition solver_entail_wit_9_split_goal_3 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem_2: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (c >= 5)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_2: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH12 : (0 <= c)) (PreH13 : (c <= 5)) (PreH14 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH15 : ((Zlength (cnt_data)) = 5)) (PreH16 : (ScoreRowState words_data i c score_mem_2 )) (PreH17 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
|--
  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
.

Definition solver_entail_wit_9_split_goal_spatial :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem_2: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (c >= 5)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k_3: Z), forall (q_2: Z), (((((0 <= k_3) /\ (k_3 < n_pre)) /\ (0 <= q_2)) /\ (q_2 < (Zlength ((Znth (k_3) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q_2) ((Znth (k_3) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((Znth (k_4) (rows) ((@nil Z))) = (c_string ((Znth (k_4) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_4) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_4) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH12 : (0 <= c)) (PreH13 : (c <= 5)) (PreH14 : ((Zlength (score_mem_2)) = (5 * n_pre ))) (PreH15 : ((Zlength (cnt_data)) = 5)) (PreH16 : (ScoreRowState words_data i c score_mem_2 )) (PreH17 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
|--
  (CharPtrArray2.full words_pre n_pre rows )
.

Definition solver_entail_wit_10 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (score_mem: (@list (@option Z))) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH12 : (ScoreBuildState words_data i score_mem )),
  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  EX (scores: (@list Z)),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ ((Zlength (scores)) = (5 * n_pre )) ”
  &&  “ (ScoreTable words_data scores ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full score (5 * n_pre ) scores )
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (score: Z) (score_mem: (@list (@option Z))) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH12 : (ScoreBuildState words_data i score_mem )),
  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  EX (scores: (@list Z)),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ ((Zlength (scores)) = (5 * n_pre )) ”
  &&  “ (ScoreTable words_data scores ) ”
  &&  (IntArray.full score (5 * n_pre ) scores )
).

Definition solver_entail_wit_11 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (scores_2: (@list Z)) (score: Z) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH7 : (ScoreTable words_data scores_2 )),
  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full score (5 * n_pre ) scores_2 )
|--
  EX (scores: (@list Z)),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 5) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((Zlength (scores)) = (5 * n_pre )) ”
  &&  “ (PreparedScoreTable words_data 0 scores ) ”
  &&  “ (AnswerState words_data 0 0 ) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000))) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full score (5 * n_pre ) scores )
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (scores_2: (@list Z)) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH7 : (ScoreTable words_data scores_2 )),
  TT && emp 
|--
  “ forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores_2) (0))) /\ ((Znth (p) (scores_2) (0)) <= 200000))) ”
  &&  “ (AnswerState words_data 0 0 ) ”
  &&  “ (PreparedScoreTable words_data 0 scores_2 ) ”
  &&  emp
).

Definition solver_entail_wit_11_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (scores_2: (@list Z)) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH7 : (ScoreTable words_data scores_2 )),
  forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores_2) (0))) /\ ((Znth (p) (scores_2) (0)) <= 200000)))
.

Definition solver_entail_wit_11_split_goal_2 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (scores_2: (@list Z)) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH7 : (ScoreTable words_data scores_2 )),
  (AnswerState words_data 0 0 )
.

Definition solver_entail_wit_11_split_goal_3 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (scores_2: (@list Z)) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH7 : (ScoreTable words_data scores_2 )),
  (PreparedScoreTable words_data 0 scores_2 )
.

Definition solver_entail_wit_12 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : (c < 5)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c <= 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : ((Zlength (scores)) = (5 * n_pre ))) (PreH12 : (PreparedScoreTable words_data c scores )) (PreH13 : (AnswerState words_data c answer )) (PreH14 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < (5 * n_pre ))) -> (((-200000) <= (Znth (p_2) (scores) (0))) /\ ((Znth (p_2) (scores) (0)) <= 200000)))),
  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full score (5 * n_pre ) scores )
|--
  EX (before: (@list Z)) (block: (@list Z)) (after: (@list Z)),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ (0 <= c) ”
  &&  “ (c < 5) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= n_pre) ”
  &&  “ (PreparedScoreTable words_data c (app (before) ((app (block) (after)))) ) ”
  &&  “ (AnswerState words_data c answer ) ”
  &&  “ ((Zlength (before)) = (c * n_pre )) ”
  &&  “ ((Zlength (block)) = n_pre) ”
  &&  “ ((Zlength (after)) = (((5 - c ) - 1 ) * n_pre )) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < (Zlength (block)))) -> (((-200000) <= (Znth (p) (block) (0))) /\ ((Znth (p) (block) (0)) <= 200000))) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.seg score 0 (c * n_pre ) before )
  **  (IntArray.full (score + ((c * n_pre ) * sizeof(INT))) n_pre block )
  **  (IntArray.seg score ((c + 1 ) * n_pre ) (5 * n_pre ) after )
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (score: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : (c < 5)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c <= 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : ((Zlength (scores)) = (5 * n_pre ))) (PreH12 : (PreparedScoreTable words_data c scores )) (PreH13 : (AnswerState words_data c answer )) (PreH14 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < (5 * n_pre ))) -> (((-200000) <= (Znth (p_2) (scores) (0))) /\ ((Znth (p_2) (scores) (0)) <= 200000)))),
  (IntArray.full score (5 * n_pre ) scores )
|--
  EX (before: (@list Z)) (block: (@list Z)) (after: (@list Z)),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ (0 <= c) ”
  &&  “ (c < 5) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= n_pre) ”
  &&  “ (PreparedScoreTable words_data c (app (before) ((app (block) (after)))) ) ”
  &&  “ (AnswerState words_data c answer ) ”
  &&  “ ((Zlength (before)) = (c * n_pre )) ”
  &&  “ ((Zlength (block)) = n_pre) ”
  &&  “ ((Zlength (after)) = (((5 - c ) - 1 ) * n_pre )) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < (Zlength (block)))) -> (((-200000) <= (Znth (p) (block) (0))) /\ ((Znth (p) (block) (0)) <= 200000))) ”
  &&  (IntArray.seg score 0 (c * n_pre ) before )
  **  (IntArray.full (score + ((c * n_pre ) * sizeof(INT))) n_pre block )
  **  (IntArray.seg score ((c + 1 ) * n_pre ) (5 * n_pre ) after )
).

Definition solver_entail_wit_13 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (before: (@list Z)) (block: (@list Z)) (after: (@list Z)) (c: Z) (answer: Z) (score: Z) (sorted: (@list Z)) (PreH1 : (Permutation block sorted )) (PreH2 : (decreasing sorted )) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (n_pre = (Zlength (words_data)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((TotalLength (words_data)) <= 200000)) (PreH8 : ((Zlength (rows)) = n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c < 5)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= n_pre)) (PreH13 : (PreparedScoreTable words_data c (app (before) ((app (block) (after)))) )) (PreH14 : (AnswerState words_data c answer )) (PreH15 : ((Zlength (before)) = (c * n_pre ))) (PreH16 : ((Zlength (block)) = n_pre)) (PreH17 : ((Zlength (after)) = (((5 - c ) - 1 ) * n_pre ))) (PreH18 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < (Zlength (block)))) -> (((-200000) <= (Znth (p_2) (block) (0))) /\ ((Znth (p_2) (block) (0)) <= 200000)))),
  (IntArray.full (score + ((c * n_pre ) * sizeof(INT))) n_pre sorted )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.seg score 0 (c * n_pre ) before )
  **  (IntArray.seg score ((c + 1 ) * n_pre ) (5 * n_pre ) after )
|--
  EX (scores: (@list Z)),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ (0 <= c) ”
  &&  “ (c < 5) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= n_pre) ”
  &&  “ ((Zlength (scores)) = (5 * n_pre )) ”
  &&  “ (PreparedScoreTable words_data (c + 1 ) scores ) ”
  &&  “ (AnswerState words_data c answer ) ”
  &&  “ (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) ) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000))) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full score (5 * n_pre ) scores )
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (before: (@list Z)) (block: (@list Z)) (after: (@list Z)) (c: Z) (answer: Z) (score: Z) (sorted: (@list Z)) (PreH1 : (Permutation block sorted )) (PreH2 : (decreasing sorted )) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (n_pre = (Zlength (words_data)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((TotalLength (words_data)) <= 200000)) (PreH8 : ((Zlength (rows)) = n_pre)) (PreH9 : (0 <= c)) (PreH10 : (c < 5)) (PreH11 : (0 <= answer)) (PreH12 : (answer <= n_pre)) (PreH13 : (PreparedScoreTable words_data c (app (before) ((app (block) (after)))) )) (PreH14 : (AnswerState words_data c answer )) (PreH15 : ((Zlength (before)) = (c * n_pre ))) (PreH16 : ((Zlength (block)) = n_pre)) (PreH17 : ((Zlength (after)) = (((5 - c ) - 1 ) * n_pre ))) (PreH18 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < (Zlength (block)))) -> (((-200000) <= (Znth (p_2) (block) (0))) /\ ((Znth (p_2) (block) (0)) <= 200000)))),
  (IntArray.full (score + ((c * n_pre ) * sizeof(INT))) n_pre sorted )
  **  (IntArray.seg score 0 (c * n_pre ) before )
  **  (IntArray.seg score ((c + 1 ) * n_pre ) (5 * n_pre ) after )
|--
  EX (scores: (@list Z)),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ (0 <= c) ”
  &&  “ (c < 5) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= n_pre) ”
  &&  “ ((Zlength (scores)) = (5 * n_pre )) ”
  &&  “ (PreparedScoreTable words_data (c + 1 ) scores ) ”
  &&  “ (AnswerState words_data c answer ) ”
  &&  “ (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) ) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000))) ”
  &&  (IntArray.full score (5 * n_pre ) scores )
).

Definition solver_entail_wit_14 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (scores_2: (@list Z)) (c: Z) (answer: Z) (score: Z) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c < 5)) (PreH8 : (0 <= answer)) (PreH9 : (answer <= n_pre)) (PreH10 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH11 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH12 : (AnswerState words_data c answer )) (PreH13 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) )) (PreH14 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < (5 * n_pre ))) -> (((-200000) <= (Znth (p_2) (scores_2) (0))) /\ ((Znth (p_2) (scores_2) (0)) <= 200000)))),
  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full score (5 * n_pre ) scores_2 )
|--
  EX (scores: (@list Z)),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ (0 <= c) ”
  &&  “ (c < 5) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= n_pre) ”
  &&  “ ((Zlength (scores)) = (5 * n_pre )) ”
  &&  “ (PreparedScoreTable words_data (c + 1 ) scores ) ”
  &&  “ (AnswerState words_data c answer ) ”
  &&  “ (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) ) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (0 <= ((c * n_pre ) + 0 )) ”
  &&  “ ((0 < n_pre) -> (((c * n_pre ) + 0 ) < (5 * n_pre ))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 200000) ”
  &&  “ (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) 0 0 ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full score (5 * n_pre ) scores )
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (scores_2: (@list Z)) (c: Z) (answer: Z) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c < 5)) (PreH8 : (0 <= answer)) (PreH9 : (answer <= n_pre)) (PreH10 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH11 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH12 : (AnswerState words_data c answer )) (PreH13 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) )) (PreH14 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < (5 * n_pre ))) -> (((-200000) <= (Znth (p_2) (scores_2) (0))) /\ ((Znth (p_2) (scores_2) (0)) <= 200000)))),
  TT && emp 
|--
  “ (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) 0 0 ) ”
  &&  “ ((0 < n_pre) -> (((c * n_pre ) + 0 ) < (5 * n_pre ))) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores_2) (0))) /\ ((Znth (p) (scores_2) (0)) <= 200000))) ”
  &&  emp
).

Definition solver_entail_wit_14_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (scores_2: (@list Z)) (c: Z) (answer: Z) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c < 5)) (PreH8 : (0 <= answer)) (PreH9 : (answer <= n_pre)) (PreH10 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH11 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH12 : (AnswerState words_data c answer )) (PreH13 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) )) (PreH14 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < (5 * n_pre ))) -> (((-200000) <= (Znth (p_2) (scores_2) (0))) /\ ((Znth (p_2) (scores_2) (0)) <= 200000)))),
  (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) 0 0 )
.

Definition solver_entail_wit_14_split_goal_2 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (scores_2: (@list Z)) (c: Z) (answer: Z) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c < 5)) (PreH8 : (0 <= answer)) (PreH9 : (answer <= n_pre)) (PreH10 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH11 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH12 : (AnswerState words_data c answer )) (PreH13 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) )) (PreH14 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < (5 * n_pre ))) -> (((-200000) <= (Znth (p_2) (scores_2) (0))) /\ ((Znth (p_2) (scores_2) (0)) <= 200000)))),
  ((0 < n_pre) -> (((c * n_pre ) + 0 ) < (5 * n_pre )))
.

Definition solver_entail_wit_14_split_goal_3 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (scores_2: (@list Z)) (c: Z) (answer: Z) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c < 5)) (PreH8 : (0 <= answer)) (PreH9 : (answer <= n_pre)) (PreH10 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH11 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH12 : (AnswerState words_data c answer )) (PreH13 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) )) (PreH14 : forall (p_2: Z), (((0 <= p_2) /\ (p_2 < (5 * n_pre ))) -> (((-200000) <= (Znth (p_2) (scores_2) (0))) /\ ((Znth (p_2) (scores_2) (0)) <= 200000)))),
  forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores_2) (0))) /\ ((Znth (p) (scores_2) (0)) <= 200000)))
.

Definition solver_entail_wit_15 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (sum: Z) (take: Z) (scores_2: (@list Z)) (answer: Z) (c: Z) (PreH1 : ((sum + (Znth ((c * n_pre ) + take ) scores_2 0) ) > 0)) (PreH2 : (take < n_pre)) (PreH3 : (n_pre = (Zlength (words_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((TotalLength (words_data)) <= 200000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c < 5)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= n_pre)) (PreH12 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH13 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH14 : (AnswerState words_data c answer )) (PreH15 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) )) (PreH16 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores_2) (0))) /\ ((Znth (p) (scores_2) (0)) <= 200000)))) (PreH17 : (0 <= take)) (PreH18 : (take <= n_pre)) (PreH19 : (0 <= ((c * n_pre ) + take ))) (PreH20 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= 200000)) (PreH23 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) take sum )),
  (IntArray.full score (5 * n_pre ) scores_2 )
  **  (CharPtrArray2.full words_pre n_pre rows )
|--
  EX (scores: (@list Z)),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ (0 <= c) ”
  &&  “ (c < 5) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= n_pre) ”
  &&  “ ((Zlength (scores)) = (5 * n_pre )) ”
  &&  “ (PreparedScoreTable words_data (c + 1 ) scores ) ”
  &&  “ (AnswerState words_data c answer ) ”
  &&  “ (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) ) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000))) ”
  &&  “ (0 <= (take + 1 )) ”
  &&  “ ((take + 1 ) <= n_pre) ”
  &&  “ (0 <= ((c * n_pre ) + (take + 1 ) )) ”
  &&  “ (((take + 1 ) < n_pre) -> (((c * n_pre ) + (take + 1 ) ) < (5 * n_pre ))) ”
  &&  “ (0 <= (sum + (Znth ((c * n_pre ) + take ) scores_2 0) )) ”
  &&  “ ((sum + (Znth ((c * n_pre ) + take ) scores_2 0) ) <= 200000) ”
  &&  “ (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) (take + 1 ) (sum + (Znth ((c * n_pre ) + take ) scores_2 0) ) ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full score (5 * n_pre ) scores )
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (sum: Z) (take: Z) (scores_2: (@list Z)) (answer: Z) (c: Z) (PreH1 : ((sum + (Znth ((c * n_pre ) + take ) scores_2 0) ) > 0)) (PreH2 : (take < n_pre)) (PreH3 : (n_pre = (Zlength (words_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((TotalLength (words_data)) <= 200000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c < 5)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= n_pre)) (PreH12 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH13 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH14 : (AnswerState words_data c answer )) (PreH15 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) )) (PreH16 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores_2) (0))) /\ ((Znth (p) (scores_2) (0)) <= 200000)))) (PreH17 : (0 <= take)) (PreH18 : (take <= n_pre)) (PreH19 : (0 <= ((c * n_pre ) + take ))) (PreH20 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= 200000)) (PreH23 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) take sum )),
  TT && emp 
|--
  “ (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) (take + 1 ) (sum + (Znth ((c * n_pre ) + take ) scores_2 0) ) ) ”
  &&  “ ((sum + (Znth ((c * n_pre ) + take ) scores_2 0) ) <= 200000) ”
  &&  “ (((take + 1 ) < n_pre) -> (((c * n_pre ) + (take + 1 ) ) < (5 * n_pre ))) ”
  &&  emp
).

Definition solver_entail_wit_15_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (sum: Z) (take: Z) (scores_2: (@list Z)) (answer: Z) (c: Z) (PreH1 : ((sum + (Znth ((c * n_pre ) + take ) scores_2 0) ) > 0)) (PreH2 : (take < n_pre)) (PreH3 : (n_pre = (Zlength (words_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((TotalLength (words_data)) <= 200000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c < 5)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= n_pre)) (PreH12 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH13 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH14 : (AnswerState words_data c answer )) (PreH15 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) )) (PreH16 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores_2) (0))) /\ ((Znth (p) (scores_2) (0)) <= 200000)))) (PreH17 : (0 <= take)) (PreH18 : (take <= n_pre)) (PreH19 : (0 <= ((c * n_pre ) + take ))) (PreH20 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= 200000)) (PreH23 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) take sum )),
  (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) (take + 1 ) (sum + (Znth ((c * n_pre ) + take ) scores_2 0) ) )
.

Definition solver_entail_wit_15_split_goal_2 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (sum: Z) (take: Z) (scores_2: (@list Z)) (answer: Z) (c: Z) (PreH1 : ((sum + (Znth ((c * n_pre ) + take ) scores_2 0) ) > 0)) (PreH2 : (take < n_pre)) (PreH3 : (n_pre = (Zlength (words_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((TotalLength (words_data)) <= 200000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c < 5)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= n_pre)) (PreH12 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH13 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH14 : (AnswerState words_data c answer )) (PreH15 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) )) (PreH16 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores_2) (0))) /\ ((Znth (p) (scores_2) (0)) <= 200000)))) (PreH17 : (0 <= take)) (PreH18 : (take <= n_pre)) (PreH19 : (0 <= ((c * n_pre ) + take ))) (PreH20 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= 200000)) (PreH23 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) take sum )),
  ((sum + (Znth ((c * n_pre ) + take ) scores_2 0) ) <= 200000)
.

Definition solver_entail_wit_15_split_goal_3 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (sum: Z) (take: Z) (scores_2: (@list Z)) (answer: Z) (c: Z) (PreH1 : ((sum + (Znth ((c * n_pre ) + take ) scores_2 0) ) > 0)) (PreH2 : (take < n_pre)) (PreH3 : (n_pre = (Zlength (words_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((TotalLength (words_data)) <= 200000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c < 5)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= n_pre)) (PreH12 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH13 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH14 : (AnswerState words_data c answer )) (PreH15 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) )) (PreH16 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores_2) (0))) /\ ((Znth (p) (scores_2) (0)) <= 200000)))) (PreH17 : (0 <= take)) (PreH18 : (take <= n_pre)) (PreH19 : (0 <= ((c * n_pre ) + take ))) (PreH20 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= 200000)) (PreH23 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) take sum )),
  (((take + 1 ) < n_pre) -> (((c * n_pre ) + (take + 1 ) ) < (5 * n_pre )))
.

Definition solver_entail_wit_16_1 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (sum: Z) (take: Z) (scores_2: (@list Z)) (answer: Z) (c: Z) (PreH1 : (take >= n_pre)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH12 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH13 : (AnswerState words_data c answer )) (PreH14 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) )) (PreH15 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores_2) (0))) /\ ((Znth (p) (scores_2) (0)) <= 200000)))) (PreH16 : (0 <= take)) (PreH17 : (take <= n_pre)) (PreH18 : (0 <= ((c * n_pre ) + take ))) (PreH19 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH20 : (0 <= sum)) (PreH21 : (sum <= 200000)) (PreH22 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) take sum )),
  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full score (5 * n_pre ) scores_2 )
|--
  EX (scores: (@list Z)),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ (0 <= c) ”
  &&  “ (c < 5) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= n_pre) ”
  &&  “ (0 <= take) ”
  &&  “ (take <= n_pre) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= 200000) ”
  &&  “ ((Zlength (scores)) = (5 * n_pre )) ”
  &&  “ (PreparedScoreTable words_data (c + 1 ) scores ) ”
  &&  “ (AnswerState words_data c answer ) ”
  &&  “ (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum ) ”
  &&  “ (LetterBest words_data (97 + c ) take ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full score (5 * n_pre ) scores )
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (sum: Z) (take: Z) (scores_2: (@list Z)) (answer: Z) (c: Z) (PreH1 : (take >= n_pre)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH12 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH13 : (AnswerState words_data c answer )) (PreH14 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) )) (PreH15 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores_2) (0))) /\ ((Znth (p) (scores_2) (0)) <= 200000)))) (PreH16 : (0 <= take)) (PreH17 : (take <= n_pre)) (PreH18 : (0 <= ((c * n_pre ) + take ))) (PreH19 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH20 : (0 <= sum)) (PreH21 : (sum <= 200000)) (PreH22 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) take sum )),
  TT && emp 
|--
  “ (LetterBest words_data (97 + c ) take ) ”
  &&  emp
).

Definition solver_entail_wit_16_1_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (sum: Z) (take: Z) (scores_2: (@list Z)) (answer: Z) (c: Z) (PreH1 : (take >= n_pre)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH12 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH13 : (AnswerState words_data c answer )) (PreH14 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) )) (PreH15 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores_2) (0))) /\ ((Znth (p) (scores_2) (0)) <= 200000)))) (PreH16 : (0 <= take)) (PreH17 : (take <= n_pre)) (PreH18 : (0 <= ((c * n_pre ) + take ))) (PreH19 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH20 : (0 <= sum)) (PreH21 : (sum <= 200000)) (PreH22 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) take sum )),
  (LetterBest words_data (97 + c ) take )
.

Definition solver_entail_wit_16_2 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (sum: Z) (take: Z) (scores_2: (@list Z)) (answer: Z) (c: Z) (PreH1 : ((sum + (Znth ((c * n_pre ) + take ) scores_2 0) ) <= 0)) (PreH2 : (take < n_pre)) (PreH3 : (n_pre = (Zlength (words_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((TotalLength (words_data)) <= 200000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c < 5)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= n_pre)) (PreH12 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH13 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH14 : (AnswerState words_data c answer )) (PreH15 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) )) (PreH16 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores_2) (0))) /\ ((Znth (p) (scores_2) (0)) <= 200000)))) (PreH17 : (0 <= take)) (PreH18 : (take <= n_pre)) (PreH19 : (0 <= ((c * n_pre ) + take ))) (PreH20 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= 200000)) (PreH23 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) take sum )),
  (IntArray.full score (5 * n_pre ) scores_2 )
  **  (CharPtrArray2.full words_pre n_pre rows )
|--
  EX (scores: (@list Z)),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ (0 <= c) ”
  &&  “ (c < 5) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= n_pre) ”
  &&  “ (0 <= take) ”
  &&  “ (take <= n_pre) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= 200000) ”
  &&  “ ((Zlength (scores)) = (5 * n_pre )) ”
  &&  “ (PreparedScoreTable words_data (c + 1 ) scores ) ”
  &&  “ (AnswerState words_data c answer ) ”
  &&  “ (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum ) ”
  &&  “ (LetterBest words_data (97 + c ) take ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full score (5 * n_pre ) scores )
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (sum: Z) (take: Z) (scores_2: (@list Z)) (answer: Z) (c: Z) (PreH1 : ((sum + (Znth ((c * n_pre ) + take ) scores_2 0) ) <= 0)) (PreH2 : (take < n_pre)) (PreH3 : (n_pre = (Zlength (words_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((TotalLength (words_data)) <= 200000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c < 5)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= n_pre)) (PreH12 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH13 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH14 : (AnswerState words_data c answer )) (PreH15 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) )) (PreH16 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores_2) (0))) /\ ((Znth (p) (scores_2) (0)) <= 200000)))) (PreH17 : (0 <= take)) (PreH18 : (take <= n_pre)) (PreH19 : (0 <= ((c * n_pre ) + take ))) (PreH20 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= 200000)) (PreH23 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) take sum )),
  TT && emp 
|--
  “ (LetterBest words_data (97 + c ) take ) ”
  &&  emp
).

Definition solver_entail_wit_16_2_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (sum: Z) (take: Z) (scores_2: (@list Z)) (answer: Z) (c: Z) (PreH1 : ((sum + (Znth ((c * n_pre ) + take ) scores_2 0) ) <= 0)) (PreH2 : (take < n_pre)) (PreH3 : (n_pre = (Zlength (words_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((TotalLength (words_data)) <= 200000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c < 5)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= n_pre)) (PreH12 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH13 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH14 : (AnswerState words_data c answer )) (PreH15 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) )) (PreH16 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores_2) (0))) /\ ((Znth (p) (scores_2) (0)) <= 200000)))) (PreH17 : (0 <= take)) (PreH18 : (take <= n_pre)) (PreH19 : (0 <= ((c * n_pre ) + take ))) (PreH20 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= 200000)) (PreH23 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) take sum )),
  (LetterBest words_data (97 + c ) take )
.

Definition solver_entail_wit_17_1 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (scores_2: (@list Z)) (c: Z) (answer: Z) (take: Z) (sum: Z) (score: Z) (PreH1 : (take > answer)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : (0 <= take)) (PreH12 : (take <= n_pre)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= 200000)) (PreH15 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH16 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH17 : (AnswerState words_data c answer )) (PreH18 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) take sum )) (PreH19 : (LetterBest words_data (97 + c ) take )),
  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full score (5 * n_pre ) scores_2 )
|--
  EX (scores: (@list Z)),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ (0 <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= 5) ”
  &&  “ (0 <= take) ”
  &&  “ (take <= n_pre) ”
  &&  “ ((Zlength (scores)) = (5 * n_pre )) ”
  &&  “ (PreparedScoreTable words_data (c + 1 ) scores ) ”
  &&  “ (AnswerState words_data (c + 1 ) take ) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000))) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full score (5 * n_pre ) scores )
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (scores_2: (@list Z)) (c: Z) (answer: Z) (take: Z) (sum: Z) (PreH1 : (take > answer)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : (0 <= take)) (PreH12 : (take <= n_pre)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= 200000)) (PreH15 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH16 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH17 : (AnswerState words_data c answer )) (PreH18 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) take sum )) (PreH19 : (LetterBest words_data (97 + c ) take )),
  TT && emp 
|--
  “ forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores_2) (0))) /\ ((Znth (p) (scores_2) (0)) <= 200000))) ”
  &&  “ (AnswerState words_data (c + 1 ) take ) ”
  &&  emp
).

Definition solver_entail_wit_17_1_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (scores_2: (@list Z)) (c: Z) (answer: Z) (take: Z) (sum: Z) (PreH1 : (take > answer)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : (0 <= take)) (PreH12 : (take <= n_pre)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= 200000)) (PreH15 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH16 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH17 : (AnswerState words_data c answer )) (PreH18 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) take sum )) (PreH19 : (LetterBest words_data (97 + c ) take )),
  forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores_2) (0))) /\ ((Znth (p) (scores_2) (0)) <= 200000)))
.

Definition solver_entail_wit_17_1_split_goal_2 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (scores_2: (@list Z)) (c: Z) (answer: Z) (take: Z) (sum: Z) (PreH1 : (take > answer)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : (0 <= take)) (PreH12 : (take <= n_pre)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= 200000)) (PreH15 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH16 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH17 : (AnswerState words_data c answer )) (PreH18 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) take sum )) (PreH19 : (LetterBest words_data (97 + c ) take )),
  (AnswerState words_data (c + 1 ) take )
.

Definition solver_entail_wit_17_2 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (scores_2: (@list Z)) (c: Z) (answer: Z) (take: Z) (sum: Z) (score: Z) (PreH1 : (take <= answer)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : (0 <= take)) (PreH12 : (take <= n_pre)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= 200000)) (PreH15 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH16 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH17 : (AnswerState words_data c answer )) (PreH18 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) take sum )) (PreH19 : (LetterBest words_data (97 + c ) take )),
  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full score (5 * n_pre ) scores_2 )
|--
  EX (scores: (@list Z)),
  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ (0 <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= 5) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= n_pre) ”
  &&  “ ((Zlength (scores)) = (5 * n_pre )) ”
  &&  “ (PreparedScoreTable words_data (c + 1 ) scores ) ”
  &&  “ (AnswerState words_data (c + 1 ) answer ) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000))) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full score (5 * n_pre ) scores )
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (scores_2: (@list Z)) (c: Z) (answer: Z) (take: Z) (sum: Z) (PreH1 : (take <= answer)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : (0 <= take)) (PreH12 : (take <= n_pre)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= 200000)) (PreH15 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH16 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH17 : (AnswerState words_data c answer )) (PreH18 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) take sum )) (PreH19 : (LetterBest words_data (97 + c ) take )),
  TT && emp 
|--
  “ forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores_2) (0))) /\ ((Znth (p) (scores_2) (0)) <= 200000))) ”
  &&  “ (AnswerState words_data (c + 1 ) answer ) ”
  &&  emp
).

Definition solver_entail_wit_17_2_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (scores_2: (@list Z)) (c: Z) (answer: Z) (take: Z) (sum: Z) (PreH1 : (take <= answer)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : (0 <= take)) (PreH12 : (take <= n_pre)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= 200000)) (PreH15 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH16 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH17 : (AnswerState words_data c answer )) (PreH18 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) take sum )) (PreH19 : (LetterBest words_data (97 + c ) take )),
  forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores_2) (0))) /\ ((Znth (p) (scores_2) (0)) <= 200000)))
.

Definition solver_entail_wit_17_2_split_goal_2 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (scores_2: (@list Z)) (c: Z) (answer: Z) (take: Z) (sum: Z) (PreH1 : (take <= answer)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : (0 <= take)) (PreH12 : (take <= n_pre)) (PreH13 : (0 <= sum)) (PreH14 : (sum <= 200000)) (PreH15 : ((Zlength (scores_2)) = (5 * n_pre ))) (PreH16 : (PreparedScoreTable words_data (c + 1 ) scores_2 )) (PreH17 : (AnswerState words_data c answer )) (PreH18 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores_2)) take sum )) (PreH19 : (LetterBest words_data (97 + c ) take )),
  (AnswerState words_data (c + 1 ) answer )
.

Definition solver_return_wit_1 :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : (c >= 5)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c <= 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : ((Zlength (scores)) = (5 * n_pre ))) (PreH12 : (PreparedScoreTable words_data c scores )) (PreH13 : (AnswerState words_data c answer )) (PreH14 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))),
  (CharPtrArray2.full words_pre n_pre rows )
|--
  “ (Spec words_data answer ) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : (c >= 5)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c <= 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : ((Zlength (scores)) = (5 * n_pre ))) (PreH12 : (PreparedScoreTable words_data c scores )) (PreH13 : (AnswerState words_data c answer )) (PreH14 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))),
  TT && emp 
|--
  “ (Spec words_data answer ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (n_pre: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : (c >= 5)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c <= 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : ((Zlength (scores)) = (5 * n_pre ))) (PreH12 : (PreparedScoreTable words_data c scores )) (PreH13 : (AnswerState words_data c answer )) (PreH14 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))),
  (Spec words_data answer )
.

Definition solver_partial_solve_wit_1_pure :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) __default__List_Z (PreH1 : (1 <= (Zlength (words_data)))) (PreH2 : ((Zlength (words_data)) <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (words_data)))) -> (0 < (Zlength ((Znth i words_data __default__List_Z)))))) (PreH4 : forall (i_2: Z), forall (j: Z), (((((0 <= i_2) /\ (i_2 < (Zlength (words_data)))) /\ (0 <= j)) /\ (j < (Zlength ((Znth i_2 words_data __default__List_Z))))) -> ((97 <= (Znth (j) ((Znth (i_2) (words_data) ((@nil Z)))) (0))) /\ ((Znth (j) ((Znth (i_2) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < n_pre)) -> ((((Znth (i_3) (rows) ((@nil Z))) = (c_string ((Znth (i_3) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (i_3) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (i_3) (words_data) ((@nil Z))))) < INT_MAX)))),
  ((( &( "score" ) )) # Ptr  |->_)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharPtrArray2.full words_pre n_pre rows )
|--
  “ (0 <= (5 * n_pre )) ”
  &&  “ (((5 * n_pre ) * sizeof(INT) ) = ((5 * n_pre ) * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_1_aux :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) __default__List_Z (PreH1 : (1 <= (Zlength (words_data)))) (PreH2 : ((Zlength (words_data)) <= 200000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (words_data)))) -> (0 < (Zlength ((Znth i words_data __default__List_Z)))))) (PreH4 : forall (i_2: Z), forall (j: Z), (((((0 <= i_2) /\ (i_2 < (Zlength (words_data)))) /\ (0 <= j)) /\ (j < (Zlength ((Znth i_2 words_data __default__List_Z))))) -> ((97 <= (Znth (j) ((Znth (i_2) (words_data) ((@nil Z)))) (0))) /\ ((Znth (j) ((Znth (i_2) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : forall (i_3: Z), (((0 <= i_3) /\ (i_3 < n_pre)) -> ((((Znth (i_3) (rows) ((@nil Z))) = (c_string ((Znth (i_3) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (i_3) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (i_3) (words_data) ((@nil Z))))) < INT_MAX)))),
  (CharPtrArray2.full words_pre n_pre rows )
|--
  “ (0 <= (5 * n_pre )) ”
  &&  “ (((5 * n_pre ) * sizeof(INT) ) = ((5 * n_pre ) * sizeof(INT) )) ”
  &&  “ (1 <= (Zlength (words_data))) ”
  &&  “ ((Zlength (words_data)) <= 200000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (words_data)))) -> (0 < (Zlength ((Znth i words_data __default__List_Z))))) ”
  &&  “ forall (i_2: Z), forall (j: Z), (((((0 <= i_2) /\ (i_2 < (Zlength (words_data)))) /\ (0 <= j)) /\ (j < (Zlength ((Znth i_2 words_data __default__List_Z))))) -> ((97 <= (Znth (j) ((Znth (i_2) (words_data) ((@nil Z)))) (0))) /\ ((Znth (j) ((Znth (i_2) (words_data) ((@nil Z)))) (0)) <= 101))) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ (n_pre = (Zlength (words_data))) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ forall (i_3: Z), (((0 <= i_3) /\ (i_3 < n_pre)) -> ((((Znth (i_3) (rows) ((@nil Z))) = (c_string ((Znth (i_3) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (i_3) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (i_3) (words_data) ((@nil Z))))) < INT_MAX))) ”
  &&  (CharPtrArray2.full words_pre n_pre rows )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2_pure :=
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score_mem: (@list (@option Z))) (row_ptr: Z) (i: Z) (score: Z) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH11 : (ScoreBuildState words_data i score_mem )),
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr ((string_length ((Znth (i) (words_data) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ ((string_length ((Znth (i) (words_data) ((@nil Z))))) < INT_MAX) ”
  &&  “ (valid_string (Znth (i) (words_data) ((@nil Z))) ) ”
) \/
(
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score_mem: (@list (@option Z))) (row_ptr: Z) (i: Z) (score: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (n_pre = (Zlength (words_data)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : ((TotalLength (words_data)) <= 200000)) (PreH9 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH15 : (ScoreBuildState words_data i score_mem )),
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr ((string_length ((Znth (i) (words_data) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ (valid_string (Znth (i) (words_data) ((@nil Z))) ) ”
  &&  “ ((string_length ((Znth (i) (words_data) ((@nil Z))))) < INT_MAX) ”
).

Definition solver_partial_solve_wit_2_pure_split_goal_1 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score_mem: (@list (@option Z))) (row_ptr: Z) (i: Z) (score: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (n_pre = (Zlength (words_data)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : ((TotalLength (words_data)) <= 200000)) (PreH9 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH15 : (ScoreBuildState words_data i score_mem )),
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr ((string_length ((Znth (i) (words_data) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ (valid_string (Znth (i) (words_data) ((@nil Z))) ) ”
.

Definition solver_partial_solve_wit_2_pure_split_goal_2 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score_mem: (@list (@option Z))) (row_ptr: Z) (i: Z) (score: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (n_pre = (Zlength (words_data)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : ((TotalLength (words_data)) <= 200000)) (PreH9 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH10 : ((Zlength (rows)) = n_pre)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH15 : (ScoreBuildState words_data i score_mem )),
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr ((string_length ((Znth (i) (words_data) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ ((string_length ((Znth (i) (words_data) ((@nil Z))))) < INT_MAX) ”
.

Definition solver_partial_solve_wit_2_aux :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score_mem: (@list (@option Z))) (row_ptr: Z) (i: Z) (score: Z) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH11 : (ScoreBuildState words_data i score_mem )),
  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr ((string_length ((Znth (i) (words_data) ((@nil Z))))) + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ ((string_length ((Znth (i) (words_data) ((@nil Z))))) < INT_MAX) ”
  &&  “ (valid_string (Znth (i) (words_data) ((@nil Z))) ) ”
  &&  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Zlength (score_mem)) = (5 * n_pre )) ”
  &&  “ (ScoreBuildState words_data i score_mem ) ”
  &&  (store_string row_ptr (Znth (i) (words_data) ((@nil Z))) )
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ))) (PreH2 : (((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ) < 5)) (PreH3 : (len <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (len >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j < len)) (PreH8 : (n_pre = (Zlength (words_data)))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((TotalLength (words_data)) <= 200000)) (PreH12 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH18 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH19 : (0 <= j)) (PreH20 : (j <= len)) (PreH21 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH22 : ((Zlength (cnt_data)) = 5)) (PreH23 : (ScoreBuildState words_data i score_mem )) (PreH24 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data )),
  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
|--
  “ (0 <= ((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 )) ”
  &&  “ (((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ) < 5) ”
  &&  “ (len <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (len >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ (j < len) ”
  &&  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (len = (Zlength ((Znth (i) (words_data) ((@nil Z)))))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= len) ”
  &&  “ ((Zlength (score_mem)) = (5 * n_pre )) ”
  &&  “ ((Zlength (cnt_data)) = 5) ”
  &&  “ (ScoreBuildState words_data i score_mem ) ”
  &&  “ (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data ) ”
  &&  (((row_ptr + (j * sizeof(CHAR)))) # Char  |-> (Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0))
  **  (CharArray.missing_i row_ptr j 0 (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
.

Definition solver_partial_solve_wit_4 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ))) (PreH2 : (((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ) < 5)) (PreH3 : (len <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (len >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j < len)) (PreH8 : (n_pre = (Zlength (words_data)))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((TotalLength (words_data)) <= 200000)) (PreH12 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH18 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH19 : (0 <= j)) (PreH20 : (j <= len)) (PreH21 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH22 : ((Zlength (cnt_data)) = 5)) (PreH23 : (ScoreBuildState words_data i score_mem )) (PreH24 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data )),
  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
|--
  “ (0 <= ((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 )) ”
  &&  “ (((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ) < 5) ”
  &&  “ (len <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (len >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ (j < len) ”
  &&  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (len = (Zlength ((Znth (i) (words_data) ((@nil Z)))))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= len) ”
  &&  “ ((Zlength (score_mem)) = (5 * n_pre )) ”
  &&  “ ((Zlength (cnt_data)) = 5) ”
  &&  “ (ScoreBuildState words_data i score_mem ) ”
  &&  “ (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data ) ”
  &&  (((( &( "cnt" ) ) + (((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 ) * sizeof(INT)))) # Int  |-> (Znth ((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 ) cnt_data 0))
  **  (IntArray.missing_i ( &( "cnt" ) ) ((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 ) 0 5 cnt_data )
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
.

Definition solver_partial_solve_wit_5 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (j: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ))) (PreH2 : (((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ) < 5)) (PreH3 : (len <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (len >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j < len)) (PreH8 : (n_pre = (Zlength (words_data)))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((TotalLength (words_data)) <= 200000)) (PreH12 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH13 : ((Zlength (rows)) = n_pre)) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH15 : (0 <= i)) (PreH16 : (i < n_pre)) (PreH17 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH18 : forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101)))) (PreH19 : (0 <= j)) (PreH20 : (j <= len)) (PreH21 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH22 : ((Zlength (cnt_data)) = 5)) (PreH23 : (ScoreBuildState words_data i score_mem )) (PreH24 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data )),
  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ (0 <= ((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 )) ”
  &&  “ (((Znth (j) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) - 97 ) < 5) ”
  &&  “ (len <= INT_MAX) ”
  &&  “ (n_pre <= INT_MAX) ”
  &&  “ (len >= INT_MIN) ”
  &&  “ (n_pre >= INT_MIN) ”
  &&  “ (j < len) ”
  &&  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (len = (Zlength ((Znth (i) (words_data) ((@nil Z)))))) ”
  &&  “ forall (q_2: Z), (((0 <= q_2) /\ (q_2 < len)) -> ((97 <= (Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0))) /\ ((Znth (q_2) ((c_string ((Znth (i) (words_data) ((@nil Z)))))) (0)) <= 101))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= len) ”
  &&  “ ((Zlength (score_mem)) = (5 * n_pre )) ”
  &&  “ ((Zlength (cnt_data)) = 5) ”
  &&  “ (ScoreBuildState words_data i score_mem ) ”
  &&  “ (CountPrefixState (Znth (i) (words_data) ((@nil Z))) j cnt_data ) ”
  &&  (((( &( "cnt" ) ) + (((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "cnt" ) ) ((Znth j (c_string ((Znth (i) (words_data) ((@nil Z))))) 0) - 97 ) 0 5 cnt_data )
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
.

Definition solver_partial_solve_wit_6 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((c * n_pre ) + i ))) (PreH2 : (((c * n_pre ) + i ) < (5 * n_pre ))) (PreH3 : (len <= INT_MAX)) (PreH4 : (len >= INT_MIN)) (PreH5 : (c < 5)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((TotalLength (words_data)) <= 200000)) (PreH10 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH16 : (0 <= c)) (PreH17 : (c <= 5)) (PreH18 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH19 : ((Zlength (cnt_data)) = 5)) (PreH20 : (ScoreRowState words_data i c score_mem )) (PreH21 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
|--
  “ (0 <= ((c * n_pre ) + i )) ”
  &&  “ (((c * n_pre ) + i ) < (5 * n_pre )) ”
  &&  “ (len <= INT_MAX) ”
  &&  “ (len >= INT_MIN) ”
  &&  “ (c < 5) ”
  &&  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (len = (Zlength ((Znth (i) (words_data) ((@nil Z)))))) ”
  &&  “ (0 <= c) ”
  &&  “ (c <= 5) ”
  &&  “ ((Zlength (score_mem)) = (5 * n_pre )) ”
  &&  “ ((Zlength (cnt_data)) = 5) ”
  &&  “ (ScoreRowState words_data i c score_mem ) ”
  &&  “ (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data ) ”
  &&  (((( &( "cnt" ) ) + (c * sizeof(INT)))) # Int  |-> (Znth c cnt_data 0))
  **  (IntArray.missing_i ( &( "cnt" ) ) c 0 5 cnt_data )
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
.

Definition solver_partial_solve_wit_7 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (row_ptr: Z) (cnt_data: (@list Z)) (score_mem: (@list (@option Z))) (c: Z) (len: Z) (i: Z) (PreH1 : (0 <= ((c * n_pre ) + i ))) (PreH2 : (((c * n_pre ) + i ) < (5 * n_pre ))) (PreH3 : (len <= INT_MAX)) (PreH4 : (len >= INT_MIN)) (PreH5 : (c < 5)) (PreH6 : (n_pre = (Zlength (words_data)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((TotalLength (words_data)) <= 200000)) (PreH10 : forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101)))) (PreH11 : ((Zlength (rows)) = n_pre)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX)))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (len = (Zlength ((Znth (i) (words_data) ((@nil Z))))))) (PreH16 : (0 <= c)) (PreH17 : (c <= 5)) (PreH18 : ((Zlength (score_mem)) = (5 * n_pre ))) (PreH19 : ((Zlength (cnt_data)) = 5)) (PreH20 : (ScoreRowState words_data i c score_mem )) (PreH21 : (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data )),
  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
  **  (IntArray.mixed_full score (5 * n_pre ) score_mem )
|--
  “ (0 <= ((c * n_pre ) + i )) ”
  &&  “ (((c * n_pre ) + i ) < (5 * n_pre )) ”
  &&  “ (len <= INT_MAX) ”
  &&  “ (len >= INT_MIN) ”
  &&  “ (c < 5) ”
  &&  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ forall (k: Z), forall (q: Z), (((((0 <= k) /\ (k < n_pre)) /\ (0 <= q)) /\ (q < (Zlength ((Znth (k) (words_data) ((@nil Z))))))) -> ((97 <= (Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0))) /\ ((Znth (q) ((Znth (k) (words_data) ((@nil Z)))) (0)) <= 101))) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth (k_2) (rows) ((@nil Z))) = (c_string ((Znth (k_2) (words_data) ((@nil Z)))))) /\ (valid_string (Znth (k_2) (words_data) ((@nil Z))) )) /\ ((string_length ((Znth (k_2) (words_data) ((@nil Z))))) < INT_MAX))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (len = (Zlength ((Znth (i) (words_data) ((@nil Z)))))) ”
  &&  “ (0 <= c) ”
  &&  “ (c <= 5) ”
  &&  “ ((Zlength (score_mem)) = (5 * n_pre )) ”
  &&  “ ((Zlength (cnt_data)) = 5) ”
  &&  “ (ScoreRowState words_data i c score_mem ) ”
  &&  “ (CountPrefixState (Znth (i) (words_data) ((@nil Z))) len cnt_data ) ”
  &&  (((score + (((c * n_pre ) + i ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i score ((c * n_pre ) + i ) 0 (5 * n_pre ) score_mem )
  **  (IntArray.full ( &( "cnt" ) ) 5 cnt_data )
  **  (CharPtrArray2.missing_i words_pre n_pre i row_ptr rows )
  **  (((words_pre + (i * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (len + 1 ) (c_string ((Znth (i) (words_data) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_8_pure :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (before: (@list Z)) (block: (@list Z)) (after: (@list Z)) (c: Z) (answer: Z) (score: Z) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c < 5)) (PreH8 : (0 <= answer)) (PreH9 : (answer <= n_pre)) (PreH10 : (PreparedScoreTable words_data c (app (before) ((app (block) (after)))) )) (PreH11 : (AnswerState words_data c answer )) (PreH12 : ((Zlength (before)) = (c * n_pre ))) (PreH13 : ((Zlength (block)) = n_pre)) (PreH14 : ((Zlength (after)) = (((5 - c ) - 1 ) * n_pre ))) (PreH15 : forall (p: Z), (((0 <= p) /\ (p < (Zlength (block)))) -> (((-200000) <= (Znth (p) (block) (0))) /\ ((Znth (p) (block) (0)) <= 200000)))),
  ((( &( "words" ) )) # Ptr  |-> words_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  ((( &( "score" ) )) # Ptr  |-> score)
  **  (IntArray.seg score 0 (c * n_pre ) before )
  **  (IntArray.full (score + ((c * n_pre ) * sizeof(INT))) n_pre block )
  **  (IntArray.seg score ((c + 1 ) * n_pre ) (5 * n_pre ) after )
|--
  “ (n_pre = (Zlength (block))) ”
  &&  “ (sizeof(INT) = sizeof(INT)) ”
.

Definition solver_partial_solve_wit_8_aux :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (before: (@list Z)) (block: (@list Z)) (after: (@list Z)) (c: Z) (answer: Z) (score: Z) (PreH1 : (n_pre = (Zlength (words_data)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((TotalLength (words_data)) <= 200000)) (PreH5 : ((Zlength (rows)) = n_pre)) (PreH6 : (0 <= c)) (PreH7 : (c < 5)) (PreH8 : (0 <= answer)) (PreH9 : (answer <= n_pre)) (PreH10 : (PreparedScoreTable words_data c (app (before) ((app (block) (after)))) )) (PreH11 : (AnswerState words_data c answer )) (PreH12 : ((Zlength (before)) = (c * n_pre ))) (PreH13 : ((Zlength (block)) = n_pre)) (PreH14 : ((Zlength (after)) = (((5 - c ) - 1 ) * n_pre ))) (PreH15 : forall (p: Z), (((0 <= p) /\ (p < (Zlength (block)))) -> (((-200000) <= (Znth (p) (block) (0))) /\ ((Znth (p) (block) (0)) <= 200000)))),
  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.seg score 0 (c * n_pre ) before )
  **  (IntArray.full (score + ((c * n_pre ) * sizeof(INT))) n_pre block )
  **  (IntArray.seg score ((c + 1 ) * n_pre ) (5 * n_pre ) after )
|--
  “ (n_pre = (Zlength (block))) ”
  &&  “ (sizeof(INT) = sizeof(INT)) ”
  &&  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ (0 <= c) ”
  &&  “ (c < 5) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= n_pre) ”
  &&  “ (PreparedScoreTable words_data c (app (before) ((app (block) (after)))) ) ”
  &&  “ (AnswerState words_data c answer ) ”
  &&  “ ((Zlength (before)) = (c * n_pre )) ”
  &&  “ ((Zlength (block)) = n_pre) ”
  &&  “ ((Zlength (after)) = (((5 - c ) - 1 ) * n_pre )) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < (Zlength (block)))) -> (((-200000) <= (Znth (p) (block) (0))) /\ ((Znth (p) (block) (0)) <= 200000))) ”
  &&  (IntArray.full (score + ((c * n_pre ) * sizeof(INT))) n_pre block )
  **  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.seg score 0 (c * n_pre ) before )
  **  (IntArray.seg score ((c + 1 ) * n_pre ) (5 * n_pre ) after )
.

Definition solver_partial_solve_wit_8 := solver_partial_solve_wit_8_pure -> solver_partial_solve_wit_8_aux.

Definition solver_partial_solve_wit_9 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (sum: Z) (take: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : (take < n_pre)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c < 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : ((Zlength (scores)) = (5 * n_pre ))) (PreH12 : (PreparedScoreTable words_data (c + 1 ) scores )) (PreH13 : (AnswerState words_data c answer )) (PreH14 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) )) (PreH15 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))) (PreH16 : (0 <= take)) (PreH17 : (take <= n_pre)) (PreH18 : (0 <= ((c * n_pre ) + take ))) (PreH19 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH20 : (0 <= sum)) (PreH21 : (sum <= 200000)) (PreH22 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum )),
  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full score (5 * n_pre ) scores )
|--
  “ (take < n_pre) ”
  &&  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ (0 <= c) ”
  &&  “ (c < 5) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= n_pre) ”
  &&  “ ((Zlength (scores)) = (5 * n_pre )) ”
  &&  “ (PreparedScoreTable words_data (c + 1 ) scores ) ”
  &&  “ (AnswerState words_data c answer ) ”
  &&  “ (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) ) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000))) ”
  &&  “ (0 <= take) ”
  &&  “ (take <= n_pre) ”
  &&  “ (0 <= ((c * n_pre ) + take )) ”
  &&  “ ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre ))) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= 200000) ”
  &&  “ (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum ) ”
  &&  (((score + (((c * n_pre ) + take ) * sizeof(INT)))) # Int  |-> (Znth ((c * n_pre ) + take ) scores 0))
  **  (IntArray.missing_i score ((c * n_pre ) + take ) 0 (5 * n_pre ) scores )
  **  (CharPtrArray2.full words_pre n_pre rows )
.

Definition solver_partial_solve_wit_10 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (sum: Z) (take: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : ((sum + (Znth ((c * n_pre ) + take ) scores 0) ) > 0)) (PreH2 : (take < n_pre)) (PreH3 : (n_pre = (Zlength (words_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((TotalLength (words_data)) <= 200000)) (PreH7 : ((Zlength (rows)) = n_pre)) (PreH8 : (0 <= c)) (PreH9 : (c < 5)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= n_pre)) (PreH12 : ((Zlength (scores)) = (5 * n_pre ))) (PreH13 : (PreparedScoreTable words_data (c + 1 ) scores )) (PreH14 : (AnswerState words_data c answer )) (PreH15 : (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) )) (PreH16 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))) (PreH17 : (0 <= take)) (PreH18 : (take <= n_pre)) (PreH19 : (0 <= ((c * n_pre ) + take ))) (PreH20 : ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre )))) (PreH21 : (0 <= sum)) (PreH22 : (sum <= 200000)) (PreH23 : (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum )),
  (IntArray.full score (5 * n_pre ) scores )
  **  (CharPtrArray2.full words_pre n_pre rows )
|--
  “ ((sum + (Znth ((c * n_pre ) + take ) scores 0) ) > 0) ”
  &&  “ (take < n_pre) ”
  &&  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ (0 <= c) ”
  &&  “ (c < 5) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= n_pre) ”
  &&  “ ((Zlength (scores)) = (5 * n_pre )) ”
  &&  “ (PreparedScoreTable words_data (c + 1 ) scores ) ”
  &&  “ (AnswerState words_data c answer ) ”
  &&  “ (decreasing (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) ) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000))) ”
  &&  “ (0 <= take) ”
  &&  “ (take <= n_pre) ”
  &&  “ (0 <= ((c * n_pre ) + take )) ”
  &&  “ ((take < n_pre) -> (((c * n_pre ) + take ) < (5 * n_pre ))) ”
  &&  “ (0 <= sum) ”
  &&  “ (sum <= 200000) ”
  &&  “ (PositivePrefixState (sublist ((c * n_pre )) (((c + 1 ) * n_pre )) (scores)) take sum ) ”
  &&  (((score + (((c * n_pre ) + take ) * sizeof(INT)))) # Int  |-> (Znth ((c * n_pre ) + take ) scores 0))
  **  (IntArray.missing_i score ((c * n_pre ) + take ) 0 (5 * n_pre ) scores )
  **  (CharPtrArray2.full words_pre n_pre rows )
.

Definition solver_partial_solve_wit_11 :=
forall (rows: (@list (@list Z))) (words_data: (@list (@list Z))) (words_pre: Z) (n_pre: Z) (score: Z) (scores: (@list Z)) (answer: Z) (c: Z) (PreH1 : (c >= 5)) (PreH2 : (n_pre = (Zlength (words_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((TotalLength (words_data)) <= 200000)) (PreH6 : ((Zlength (rows)) = n_pre)) (PreH7 : (0 <= c)) (PreH8 : (c <= 5)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= n_pre)) (PreH11 : ((Zlength (scores)) = (5 * n_pre ))) (PreH12 : (PreparedScoreTable words_data c scores )) (PreH13 : (AnswerState words_data c answer )) (PreH14 : forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000)))),
  (CharPtrArray2.full words_pre n_pre rows )
  **  (IntArray.full score (5 * n_pre ) scores )
|--
  “ (c >= 5) ”
  &&  “ (n_pre = (Zlength (words_data))) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 200000) ”
  &&  “ ((TotalLength (words_data)) <= 200000) ”
  &&  “ ((Zlength (rows)) = n_pre) ”
  &&  “ (0 <= c) ”
  &&  “ (c <= 5) ”
  &&  “ (0 <= answer) ”
  &&  “ (answer <= n_pre) ”
  &&  “ ((Zlength (scores)) = (5 * n_pre )) ”
  &&  “ (PreparedScoreTable words_data c scores ) ”
  &&  “ (AnswerState words_data c answer ) ”
  &&  “ forall (p: Z), (((0 <= p) /\ (p < (5 * n_pre ))) -> (((-200000) <= (Znth (p) (scores) (0))) /\ ((Znth (p) (scores) (0)) <= 200000))) ”
  &&  (IntArray.full score (5 * (Zlength (words_data)) ) scores )
  **  (CharPtrArray2.full words_pre n_pre rows )
.

Module Type VC_Correct.

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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Axiom proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Axiom proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Axiom proof_of_solver_entail_wit_14 : solver_entail_wit_14.
Axiom proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Axiom proof_of_solver_entail_wit_16_1 : solver_entail_wit_16_1.
Axiom proof_of_solver_entail_wit_16_2 : solver_entail_wit_16_2.
Axiom proof_of_solver_entail_wit_17_1 : solver_entail_wit_17_1.
Axiom proof_of_solver_entail_wit_17_2 : solver_entail_wit_17_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8_pure : solver_partial_solve_wit_8_pure.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.

End VC_Correct.
