From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P018_1146B_hate_a_lib.
Local Open Scope sac.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (string_length (given_data)))) (PreH2 : (retval = out_pre)) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (valid_string given_data )) (PreH7 : ((string_length (given_data)) = (Zlength (given_data)))) (PreH8 : ((string_length (given_data)) < INT_MAX)),
  ((( &( "k" ) )) # Int  |->_)
  **  (store_string out_pre given_data )
  **  (CharArray.full given_pre ((string_length (given_data)) + 1 ) (c_string (given_data)) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_seg out_pre ((string_length (given_data)) + 1 ) 100005 )
  **  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (string_length (given_data)))) (PreH2 : (retval = out_pre)) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (valid_string given_data )) (PreH7 : ((string_length (given_data)) = (Zlength (given_data)))) (PreH8 : ((string_length (given_data)) < INT_MAX)),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (store_string out_pre given_data )
  **  (CharArray.full given_pre ((string_length (given_data)) + 1 ) (c_string (given_data)) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_seg out_pre ((string_length (given_data)) + 1 ) 100005 )
  **  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (filtered: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered)))) (PreH11 : (FilteredPrefix given_data i filtered )),
  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ (97 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solver_safety_wit_4 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (filtered: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) <> 97)) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered)))) (PreH12 : (FilteredPrefix given_data i filtered )),
  (CharArray.full ( &( "stripped" ) ) (k + 1 ) (app (filtered) ((cons ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "stripped" ) ) (k + 1 ) 100005 )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
|--
  “ ((k + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_5 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (filtered: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) <> 97)) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered)))) (PreH12 : (FilteredPrefix given_data i filtered )),
  (CharArray.full ( &( "stripped" ) ) (k + 1 ) (app (filtered) ((cons ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "stripped" ) ) (k + 1 ) 100005 )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_6 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (filtered: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) = 97)) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered)))) (PreH12 : (FilteredPrefix given_data i filtered )),
  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_7 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (filtered: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered)))) (PreH11 : (FilteredPrefix given_data i filtered )),
  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_8 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (filtered: (@list Z)) (k: Z) (i: Z) (n: Z) (filtered_2: (@list Z)) (PreH1 : (k = (Zlength (filtered_2)))) (PreH2 : (i >= n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered)))) (PreH12 : (FilteredPrefix given_data i filtered )) (PreH13 : ((Z.land k 1) <> 0)),
  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 :=
(
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (filtered: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered)))) (PreH11 : (FilteredPrefix given_data i filtered )) (PreH12 : ((Z.land k 1) = 0)),
  ((( &( "prefix" ) )) # Int  |->_)
  **  ((( &( "suffix" ) )) # Int  |-> (k ÷ 2 ))
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ ((n - (k ÷ 2 ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n - (k ÷ 2 ) )) ”
) \/
(
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (filtered: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered)))) (PreH11 : (FilteredPrefix given_data i filtered )) (PreH12 : ((Z.land k 1) = 0)),
  ((( &( "prefix" ) )) # Int  |->_)
  **  ((( &( "suffix" ) )) # Int  |-> (k ÷ 2 ))
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ ((n - (k ÷ 2 ) ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n - (k ÷ 2 ) )) ”
).

Definition solver_safety_wit_9_split_goal_1 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (filtered: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered)))) (PreH11 : (FilteredPrefix given_data i filtered )) (PreH12 : ((Z.land k 1) = 0)),
  ((( &( "prefix" ) )) # Int  |->_)
  **  ((( &( "suffix" ) )) # Int  |-> (k ÷ 2 ))
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ ((n - (k ÷ 2 ) ) <= INT_MAX) ”
.

Definition solver_safety_wit_9_split_goal_2 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (filtered: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered)))) (PreH11 : (FilteredPrefix given_data i filtered )) (PreH12 : ((Z.land k 1) = 0)),
  ((( &( "prefix" ) )) # Int  |->_)
  **  ((( &( "suffix" ) )) # Int  |-> (k ÷ 2 ))
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ ((INT_MIN) <= (n - (k ÷ 2 ) )) ”
.

Definition solver_safety_wit_10 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (filtered: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered)))) (PreH11 : (FilteredPrefix given_data i filtered )) (PreH12 : ((Z.land k 1) = 0)),
  ((( &( "suffix" ) )) # Int  |->_)
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ ((k <> (INT_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_11 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (filtered: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered)))) (PreH11 : (FilteredPrefix given_data i filtered )) (PreH12 : ((Z.land k 1) = 0)),
  ((( &( "suffix" ) )) # Int  |->_)
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_12 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (0 <= k)) (PreH7 : (k <= n)) (PreH8 : (k = (Zlength (filtered)))) (PreH9 : (FilteredPrefix given_data n filtered )) (PreH10 : (0 <= suffix)) (PreH11 : (k = (2 * suffix ))) (PreH12 : (prefix = (n - suffix ))) (PreH13 : (0 <= prefix)) (PreH14 : (prefix <= n)) (PreH15 : (prefix <= i)) (PreH16 : (i <= n)) (PreH17 : (NoAInterval given_data prefix i )),
  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "prefix" ) )) # Int  |-> prefix)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ (97 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solver_safety_wit_13 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (filtered_2: (@list Z)) (PreH1 : (k = (Zlength (filtered_2)))) (PreH2 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) = 97)) (PreH3 : (i < n)) (PreH4 : (n = (Zlength (given_data)))) (PreH5 : (1 <= (Zlength (given_data)))) (PreH6 : ((Zlength (given_data)) <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n)) (PreH10 : (k = (Zlength (filtered)))) (PreH11 : (FilteredPrefix given_data n filtered )) (PreH12 : (0 <= suffix)) (PreH13 : (k = (2 * suffix ))) (PreH14 : (prefix = (n - suffix ))) (PreH15 : (0 <= prefix)) (PreH16 : (prefix <= n)) (PreH17 : (prefix <= i)) (PreH18 : (i <= n)) (PreH19 : (NoAInterval given_data prefix i )),
  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "prefix" ) )) # Int  |-> prefix)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_14 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (PreH1 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) <> 97)) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= k)) (PreH8 : (k <= n)) (PreH9 : (k = (Zlength (filtered)))) (PreH10 : (FilteredPrefix given_data n filtered )) (PreH11 : (0 <= suffix)) (PreH12 : (k = (2 * suffix ))) (PreH13 : (prefix = (n - suffix ))) (PreH14 : (0 <= prefix)) (PreH15 : (prefix <= n)) (PreH16 : (prefix <= i)) (PreH17 : (i <= n)) (PreH18 : (NoAInterval given_data prefix i )),
  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "prefix" ) )) # Int  |-> prefix)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_15 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (0 <= k)) (PreH7 : (k <= n)) (PreH8 : (k = (Zlength (filtered)))) (PreH9 : (FilteredPrefix given_data n filtered )) (PreH10 : (0 <= suffix)) (PreH11 : (k = (2 * suffix ))) (PreH12 : (prefix = (n - suffix ))) (PreH13 : (0 <= prefix)) (PreH14 : (prefix <= n)) (PreH15 : (prefix <= i)) (PreH16 : (i <= n)) (PreH17 : (NoAInterval given_data prefix i )),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "prefix" ) )) # Int  |-> prefix)
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_16 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (PreH1 : (i < suffix)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (0 <= k)) (PreH7 : (k <= n)) (PreH8 : (k = (Zlength (filtered)))) (PreH9 : (FilteredPrefix given_data n filtered )) (PreH10 : (0 <= suffix)) (PreH11 : (k = (2 * suffix ))) (PreH12 : (prefix = (n - suffix ))) (PreH13 : (0 <= prefix)) (PreH14 : (prefix <= n)) (PreH15 : (NoAInterval given_data prefix n )) (PreH16 : (0 <= i)) (PreH17 : (i <= suffix)) (PreH18 : (MatchedSuffixPrefix filtered given_data prefix i )),
  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "prefix" ) )) # Int  |-> prefix)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ ((prefix + i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (prefix + i )) ”
.

Definition solver_safety_wit_17 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (filtered_2: (@list Z)) (PreH1 : (k = (Zlength (filtered_2)))) (PreH2 : ((Znth i filtered 0) <> (Znth (prefix + i ) (app (given_data) ((cons (0) ((@nil Z))))) 0))) (PreH3 : (i < suffix)) (PreH4 : (n = (Zlength (given_data)))) (PreH5 : (1 <= (Zlength (given_data)))) (PreH6 : ((Zlength (given_data)) <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n)) (PreH10 : (k = (Zlength (filtered)))) (PreH11 : (FilteredPrefix given_data n filtered )) (PreH12 : (0 <= suffix)) (PreH13 : (k = (2 * suffix ))) (PreH14 : (prefix = (n - suffix ))) (PreH15 : (0 <= prefix)) (PreH16 : (prefix <= n)) (PreH17 : (NoAInterval given_data prefix n )) (PreH18 : (0 <= i)) (PreH19 : (i <= suffix)) (PreH20 : (MatchedSuffixPrefix filtered given_data prefix i )),
  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "prefix" ) )) # Int  |-> prefix)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_18 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (PreH1 : (i >= suffix)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (0 <= k)) (PreH7 : (k <= n)) (PreH8 : (k = (Zlength (filtered)))) (PreH9 : (FilteredPrefix given_data n filtered )) (PreH10 : (0 <= suffix)) (PreH11 : (k = (2 * suffix ))) (PreH12 : (prefix = (n - suffix ))) (PreH13 : (0 <= prefix)) (PreH14 : (prefix <= n)) (PreH15 : (NoAInterval given_data prefix n )) (PreH16 : (0 <= i)) (PreH17 : (i <= suffix)) (PreH18 : (MatchedSuffixPrefix filtered given_data prefix i )),
  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "prefix" ) )) # Int  |-> prefix)
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_19 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (PreH1 : ((Znth i filtered 0) = (Znth (prefix + i ) (app (given_data) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (i < suffix)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= k)) (PreH8 : (k <= n)) (PreH9 : (k = (Zlength (filtered)))) (PreH10 : (FilteredPrefix given_data n filtered )) (PreH11 : (0 <= suffix)) (PreH12 : (k = (2 * suffix ))) (PreH13 : (prefix = (n - suffix ))) (PreH14 : (0 <= prefix)) (PreH15 : (prefix <= n)) (PreH16 : (NoAInterval given_data prefix n )) (PreH17 : (0 <= i)) (PreH18 : (i <= suffix)) (PreH19 : (MatchedSuffixPrefix filtered given_data prefix i )),
  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "prefix" ) )) # Int  |-> prefix)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_20 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (filtered_2: (@list Z)) (PreH1 : (k = (Zlength (filtered_2)))) (PreH2 : (i >= suffix)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= k)) (PreH8 : (k <= n)) (PreH9 : (k = (Zlength (filtered)))) (PreH10 : (FilteredPrefix given_data n filtered )) (PreH11 : (0 <= suffix)) (PreH12 : (k = (2 * suffix ))) (PreH13 : (prefix = (n - suffix ))) (PreH14 : (0 <= prefix)) (PreH15 : (prefix <= n)) (PreH16 : (NoAInterval given_data prefix n )) (PreH17 : (0 <= i)) (PreH18 : (i <= suffix)) (PreH19 : (MatchedSuffixPrefix filtered given_data prefix i )),
  ((( &( "k" ) )) # Int  |-> k)
  **  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (replace_Znth (prefix) (0) ((app (given_data) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "prefix" ) )) # Int  |-> prefix)
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 :=
(
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (PreH1 : (1 <= (Zlength (given_data)))) (PreH2 : ((Zlength (given_data)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (given_data)))) -> ((97 <= (Znth i given_data 0)) /\ ((Znth i given_data 0) <= 122)))),
  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 100005 )
|--
  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (valid_string given_data ) ”
  &&  “ ((string_length (given_data)) = (Zlength (given_data))) ”
  &&  “ ((string_length (given_data)) < INT_MAX) ”
  &&  (store_string given_pre given_data )
  **  (CharArray.undef_full out_pre ((string_length (given_data)) + 1 ) )
  **  (CharArray.undef_seg out_pre ((string_length (given_data)) + 1 ) 100005 )
  **  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
) \/
(
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (PreH1 : (1 <= (Zlength (given_data)))) (PreH2 : ((Zlength (given_data)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (given_data)))) -> ((97 <= (Znth i given_data 0)) /\ ((Znth i given_data 0) <= 122)))),
  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 100005 )
|--
  “ ((string_length (given_data)) < INT_MAX) ”
  &&  “ ((string_length (given_data)) = (Zlength (given_data))) ”
  &&  “ (valid_string given_data ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  (CharArray.full given_pre ((string_length (given_data)) + 1 ) (c_string (given_data)) )
  **  (CharArray.undef_full out_pre ((string_length (given_data)) + 1 ) )
  **  (CharArray.undef_seg out_pre ((string_length (given_data)) + 1 ) 100005 )
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (PreH1 : (1 <= (Zlength (given_data)))) (PreH2 : ((Zlength (given_data)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (given_data)))) -> ((97 <= (Znth i given_data 0)) /\ ((Znth i given_data 0) <= 122)))),
  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 100005 )
|--
  “ ((string_length (given_data)) < INT_MAX) ”
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (PreH1 : (1 <= (Zlength (given_data)))) (PreH2 : ((Zlength (given_data)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (given_data)))) -> ((97 <= (Znth i given_data 0)) /\ ((Znth i given_data 0) <= 122)))),
  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 100005 )
|--
  “ ((string_length (given_data)) = (Zlength (given_data))) ”
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (PreH1 : (1 <= (Zlength (given_data)))) (PreH2 : ((Zlength (given_data)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (given_data)))) -> ((97 <= (Znth i given_data 0)) /\ ((Znth i given_data 0) <= 122)))),
  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 100005 )
|--
  “ (valid_string given_data ) ”
.

Definition solver_entail_wit_1_split_goal_4 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (PreH1 : (1 <= (Zlength (given_data)))) (PreH2 : ((Zlength (given_data)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (given_data)))) -> ((97 <= (Znth i given_data 0)) /\ ((Znth i given_data 0) <= 122)))),
  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 100005 )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
.

Definition solver_entail_wit_1_split_goal_spatial :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (PreH1 : (1 <= (Zlength (given_data)))) (PreH2 : ((Zlength (given_data)) <= 100000)) (PreH3 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (given_data)))) -> ((97 <= (Znth i given_data 0)) /\ ((Znth i given_data 0) <= 122)))),
  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full out_pre 100005 )
|--
  (CharArray.full given_pre ((string_length (given_data)) + 1 ) (c_string (given_data)) )
  **  (CharArray.undef_full out_pre ((string_length (given_data)) + 1 ) )
  **  (CharArray.undef_seg out_pre ((string_length (given_data)) + 1 ) 100005 )
.

Definition solver_entail_wit_2 :=
(
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (string_length (given_data)))) (PreH2 : (retval_2 = out_pre)) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (valid_string given_data )) (PreH7 : ((string_length (given_data)) = (Zlength (given_data)))) (PreH8 : ((string_length (given_data)) < INT_MAX)),
  (store_string out_pre given_data )
  **  (CharArray.full given_pre ((string_length (given_data)) + 1 ) (c_string (given_data)) )
  **  (CharArray.undef_seg out_pre ((string_length (given_data)) + 1 ) 100005 )
  **  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
|--
  EX (filtered: (@list Z)),
  “ (retval = (Zlength (given_data))) ”
  &&  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= retval) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 = (Zlength (filtered))) ”
  &&  “ (FilteredPrefix given_data 0 filtered ) ”
  &&  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) 0 filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) 0 100005 )
) \/
(
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (string_length (given_data)))) (PreH2 : (retval_2 = out_pre)) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (valid_string given_data )) (PreH7 : ((string_length (given_data)) = (Zlength (given_data)))) (PreH8 : ((string_length (given_data)) < INT_MAX)),
  (CharArray.full out_pre ((string_length (given_data)) + 1 ) (c_string (given_data)) )
  **  (CharArray.full given_pre ((string_length (given_data)) + 1 ) (c_string (given_data)) )
|--
  “ (FilteredPrefix given_data 0 (@nil Z) ) ”
  &&  “ (0 = (Zlength ((@nil Z)))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (string_length (given_data)))) (PreH2 : (retval_2 = out_pre)) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (valid_string given_data )) (PreH7 : ((string_length (given_data)) = (Zlength (given_data)))) (PreH8 : ((string_length (given_data)) < INT_MAX)),
  (CharArray.full out_pre ((string_length (given_data)) + 1 ) (c_string (given_data)) )
  **  (CharArray.full given_pre ((string_length (given_data)) + 1 ) (c_string (given_data)) )
|--
  “ (FilteredPrefix given_data 0 (@nil Z) ) ”
.

Definition solver_entail_wit_2_split_goal_2 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (string_length (given_data)))) (PreH2 : (retval_2 = out_pre)) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (valid_string given_data )) (PreH7 : ((string_length (given_data)) = (Zlength (given_data)))) (PreH8 : ((string_length (given_data)) < INT_MAX)),
  (CharArray.full out_pre ((string_length (given_data)) + 1 ) (c_string (given_data)) )
  **  (CharArray.full given_pre ((string_length (given_data)) + 1 ) (c_string (given_data)) )
|--
  “ (0 = (Zlength ((@nil Z)))) ”
.

Definition solver_entail_wit_2_split_goal_3 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (string_length (given_data)))) (PreH2 : (retval_2 = out_pre)) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (valid_string given_data )) (PreH7 : ((string_length (given_data)) = (Zlength (given_data)))) (PreH8 : ((string_length (given_data)) < INT_MAX)),
  (CharArray.full out_pre ((string_length (given_data)) + 1 ) (c_string (given_data)) )
  **  (CharArray.full given_pre ((string_length (given_data)) + 1 ) (c_string (given_data)) )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
.

Definition solver_entail_wit_2_split_goal_spatial :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (string_length (given_data)))) (PreH2 : (retval_2 = out_pre)) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (valid_string given_data )) (PreH7 : ((string_length (given_data)) = (Zlength (given_data)))) (PreH8 : ((string_length (given_data)) < INT_MAX)),
  (CharArray.full out_pre ((string_length (given_data)) + 1 ) (c_string (given_data)) )
  **  (CharArray.full given_pre ((string_length (given_data)) + 1 ) (c_string (given_data)) )
|--
  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
.

Definition solver_entail_wit_3_1 :=
(
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (filtered_2: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) <> 97)) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_2)))) (PreH12 : (FilteredPrefix given_data i filtered_2 )),
  (CharArray.full ( &( "stripped" ) ) (k + 1 ) (app (filtered_2) ((cons ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "stripped" ) ) (k + 1 ) 100005 )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
|--
  EX (filtered: (@list Z)),
  “ (n = (Zlength (given_data))) ”
  &&  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n) ”
  &&  “ (0 <= (k + 1 )) ”
  &&  “ ((k + 1 ) <= (i + 1 )) ”
  &&  “ ((k + 1 ) = (Zlength (filtered))) ”
  &&  “ (FilteredPrefix given_data (i + 1 ) filtered ) ”
  &&  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) (k + 1 ) filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) (k + 1 ) 100005 )
) \/
(
forall (given_data: (@list Z)) (filtered_2: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) <> 97)) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_2)))) (PreH12 : (FilteredPrefix given_data i filtered_2 )),
  TT && emp 
|--
  “ (FilteredPrefix given_data (i + 1 ) (app (filtered_2) ((cons ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) ) ”
  &&  “ ((k + 1 ) = (Zlength ((app (filtered_2) ((cons ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0)) ((@nil Z)))))))) ”
  &&  emp
).

Definition solver_entail_wit_3_1_split_goal_1 :=
forall (given_data: (@list Z)) (filtered_2: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) <> 97)) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_2)))) (PreH12 : (FilteredPrefix given_data i filtered_2 )),
  (FilteredPrefix given_data (i + 1 ) (app (filtered_2) ((cons ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
.

Definition solver_entail_wit_3_1_split_goal_2 :=
forall (given_data: (@list Z)) (filtered_2: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) <> 97)) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_2)))) (PreH12 : (FilteredPrefix given_data i filtered_2 )),
  ((k + 1 ) = (Zlength ((app (filtered_2) ((cons ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))))))
.

Definition solver_entail_wit_3_2 :=
(
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (filtered_2: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) = 97)) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_2)))) (PreH12 : (FilteredPrefix given_data i filtered_2 )),
  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered_2 )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  EX (filtered: (@list Z)),
  “ (n = (Zlength (given_data))) ”
  &&  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= (i + 1 )) ”
  &&  “ (k = (Zlength (filtered))) ”
  &&  “ (FilteredPrefix given_data (i + 1 ) filtered ) ”
  &&  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
) \/
(
forall (given_data: (@list Z)) (filtered_2: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) = 97)) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_2)))) (PreH12 : (FilteredPrefix given_data i filtered_2 )),
  TT && emp 
|--
  “ (FilteredPrefix given_data (i + 1 ) filtered_2 ) ”
  &&  emp
).

Definition solver_entail_wit_3_2_split_goal_1 :=
forall (given_data: (@list Z)) (filtered_2: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) = 97)) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_2)))) (PreH12 : (FilteredPrefix given_data i filtered_2 )),
  (FilteredPrefix given_data (i + 1 ) filtered_2 )
.

Definition solver_entail_wit_4 :=
(
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (filtered_2: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered_2)))) (PreH11 : (FilteredPrefix given_data i filtered_2 )) (PreH12 : ((Z.land k 1) = 0)),
  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered_2 )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  EX (filtered: (@list Z)),
  “ (n = (Zlength (given_data))) ”
  &&  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= n) ”
  &&  “ (k = (Zlength (filtered))) ”
  &&  “ (FilteredPrefix given_data n filtered ) ”
  &&  “ (0 <= (k ÷ 2 )) ”
  &&  “ (k = (2 * (k ÷ 2 ) )) ”
  &&  “ ((n - (k ÷ 2 ) ) = (n - (k ÷ 2 ) )) ”
  &&  “ (0 <= (n - (k ÷ 2 ) )) ”
  &&  “ ((n - (k ÷ 2 ) ) <= n) ”
  &&  “ ((n - (k ÷ 2 ) ) <= (n - (k ÷ 2 ) )) ”
  &&  “ ((n - (k ÷ 2 ) ) <= n) ”
  &&  “ (NoAInterval given_data (n - (k ÷ 2 ) ) (n - (k ÷ 2 ) ) ) ”
  &&  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
) \/
(
forall (given_data: (@list Z)) (filtered_2: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered_2)))) (PreH11 : (FilteredPrefix given_data i filtered_2 )) (PreH12 : ((Z.land k 1) = 0)),
  TT && emp 
|--
  “ (NoAInterval given_data (n - (k ÷ 2 ) ) (n - (k ÷ 2 ) ) ) ”
  &&  “ ((n - (k ÷ 2 ) ) <= n) ”
  &&  “ ((n - (k ÷ 2 ) ) <= n) ”
  &&  “ (0 <= (n - (k ÷ 2 ) )) ”
  &&  “ (k = (2 * (k ÷ 2 ) )) ”
  &&  “ (0 <= (k ÷ 2 )) ”
  &&  “ (FilteredPrefix given_data n filtered_2 ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 :=
forall (given_data: (@list Z)) (filtered_2: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered_2)))) (PreH11 : (FilteredPrefix given_data i filtered_2 )) (PreH12 : ((Z.land k 1) = 0)),
  (NoAInterval given_data (n - (k ÷ 2 ) ) (n - (k ÷ 2 ) ) )
.

Definition solver_entail_wit_4_split_goal_2 :=
forall (given_data: (@list Z)) (filtered_2: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered_2)))) (PreH11 : (FilteredPrefix given_data i filtered_2 )) (PreH12 : ((Z.land k 1) = 0)),
  ((n - (k ÷ 2 ) ) <= n)
.

Definition solver_entail_wit_4_split_goal_3 :=
forall (given_data: (@list Z)) (filtered_2: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered_2)))) (PreH11 : (FilteredPrefix given_data i filtered_2 )) (PreH12 : ((Z.land k 1) = 0)),
  ((n - (k ÷ 2 ) ) <= n)
.

Definition solver_entail_wit_4_split_goal_4 :=
forall (given_data: (@list Z)) (filtered_2: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered_2)))) (PreH11 : (FilteredPrefix given_data i filtered_2 )) (PreH12 : ((Z.land k 1) = 0)),
  (0 <= (n - (k ÷ 2 ) ))
.

Definition solver_entail_wit_4_split_goal_5 :=
forall (given_data: (@list Z)) (filtered_2: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered_2)))) (PreH11 : (FilteredPrefix given_data i filtered_2 )) (PreH12 : ((Z.land k 1) = 0)),
  (k = (2 * (k ÷ 2 ) ))
.

Definition solver_entail_wit_4_split_goal_6 :=
forall (given_data: (@list Z)) (filtered_2: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered_2)))) (PreH11 : (FilteredPrefix given_data i filtered_2 )) (PreH12 : ((Z.land k 1) = 0)),
  (0 <= (k ÷ 2 ))
.

Definition solver_entail_wit_4_split_goal_7 :=
forall (given_data: (@list Z)) (filtered_2: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered_2)))) (PreH11 : (FilteredPrefix given_data i filtered_2 )) (PreH12 : ((Z.land k 1) = 0)),
  (FilteredPrefix given_data n filtered_2 )
.

Definition solver_entail_wit_4_split_goal_8 :=
forall (given_data: (@list Z)) (filtered_2: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered_2)))) (PreH11 : (FilteredPrefix given_data i filtered_2 )) (PreH12 : ((Z.land k 1) = 0)),
  forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))
.

Definition solver_entail_wit_5 :=
(
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered_2: (@list Z)) (k: Z) (n: Z) (PreH1 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) <> 97)) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= k)) (PreH8 : (k <= n)) (PreH9 : (k = (Zlength (filtered_2)))) (PreH10 : (FilteredPrefix given_data n filtered_2 )) (PreH11 : (0 <= suffix)) (PreH12 : (k = (2 * suffix ))) (PreH13 : (prefix = (n - suffix ))) (PreH14 : (0 <= prefix)) (PreH15 : (prefix <= n)) (PreH16 : (prefix <= i)) (PreH17 : (i <= n)) (PreH18 : (NoAInterval given_data prefix i )),
  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered_2 )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  EX (filtered: (@list Z)),
  “ (n = (Zlength (given_data))) ”
  &&  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= n) ”
  &&  “ (k = (Zlength (filtered))) ”
  &&  “ (FilteredPrefix given_data n filtered ) ”
  &&  “ (0 <= suffix) ”
  &&  “ (k = (2 * suffix )) ”
  &&  “ (prefix = (n - suffix )) ”
  &&  “ (0 <= prefix) ”
  &&  “ (prefix <= n) ”
  &&  “ (prefix <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n) ”
  &&  “ (NoAInterval given_data prefix (i + 1 ) ) ”
  &&  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
) \/
(
forall (given_data: (@list Z)) (i: Z) (prefix: Z) (suffix: Z) (filtered_2: (@list Z)) (k: Z) (n: Z) (PreH1 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) <> 97)) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= k)) (PreH8 : (k <= n)) (PreH9 : (k = (Zlength (filtered_2)))) (PreH10 : (FilteredPrefix given_data n filtered_2 )) (PreH11 : (0 <= suffix)) (PreH12 : (k = (2 * suffix ))) (PreH13 : (prefix = (n - suffix ))) (PreH14 : (0 <= prefix)) (PreH15 : (prefix <= n)) (PreH16 : (prefix <= i)) (PreH17 : (i <= n)) (PreH18 : (NoAInterval given_data prefix i )),
  TT && emp 
|--
  “ (NoAInterval given_data (n - suffix ) (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 :=
forall (given_data: (@list Z)) (i: Z) (prefix: Z) (suffix: Z) (filtered_2: (@list Z)) (k: Z) (n: Z) (PreH1 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) <> 97)) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= k)) (PreH8 : (k <= n)) (PreH9 : (k = (Zlength (filtered_2)))) (PreH10 : (FilteredPrefix given_data n filtered_2 )) (PreH11 : (0 <= suffix)) (PreH12 : (k = (2 * suffix ))) (PreH13 : (prefix = (n - suffix ))) (PreH14 : (0 <= prefix)) (PreH15 : (prefix <= n)) (PreH16 : (prefix <= i)) (PreH17 : (i <= n)) (PreH18 : (NoAInterval given_data prefix i )),
  (NoAInterval given_data (n - suffix ) (i + 1 ) )
.

Definition solver_entail_wit_6 :=
(
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered_2: (@list Z)) (k: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (0 <= k)) (PreH7 : (k <= n)) (PreH8 : (k = (Zlength (filtered_2)))) (PreH9 : (FilteredPrefix given_data n filtered_2 )) (PreH10 : (0 <= suffix)) (PreH11 : (k = (2 * suffix ))) (PreH12 : (prefix = (n - suffix ))) (PreH13 : (0 <= prefix)) (PreH14 : (prefix <= n)) (PreH15 : (prefix <= i)) (PreH16 : (i <= n)) (PreH17 : (NoAInterval given_data prefix i )),
  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered_2 )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  EX (filtered: (@list Z)),
  “ (n = (Zlength (given_data))) ”
  &&  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= n) ”
  &&  “ (k = (Zlength (filtered))) ”
  &&  “ (FilteredPrefix given_data n filtered ) ”
  &&  “ (0 <= suffix) ”
  &&  “ (k = (2 * suffix )) ”
  &&  “ (prefix = (n - suffix )) ”
  &&  “ (0 <= prefix) ”
  &&  “ (prefix <= n) ”
  &&  “ (NoAInterval given_data prefix n ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= suffix) ”
  &&  “ (MatchedSuffixPrefix filtered given_data prefix 0 ) ”
  &&  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
) \/
(
forall (given_data: (@list Z)) (i: Z) (prefix: Z) (suffix: Z) (filtered_2: (@list Z)) (k: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (0 <= k)) (PreH7 : (k <= n)) (PreH8 : (k = (Zlength (filtered_2)))) (PreH9 : (FilteredPrefix given_data n filtered_2 )) (PreH10 : (0 <= suffix)) (PreH11 : (k = (2 * suffix ))) (PreH12 : (prefix = (n - suffix ))) (PreH13 : (0 <= prefix)) (PreH14 : (prefix <= n)) (PreH15 : (prefix <= i)) (PreH16 : (i <= n)) (PreH17 : (NoAInterval given_data prefix i )),
  TT && emp 
|--
  “ (MatchedSuffixPrefix filtered_2 given_data (n - suffix ) 0 ) ”
  &&  “ (NoAInterval given_data (n - suffix ) n ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 :=
forall (given_data: (@list Z)) (i: Z) (prefix: Z) (suffix: Z) (filtered_2: (@list Z)) (k: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (0 <= k)) (PreH7 : (k <= n)) (PreH8 : (k = (Zlength (filtered_2)))) (PreH9 : (FilteredPrefix given_data n filtered_2 )) (PreH10 : (0 <= suffix)) (PreH11 : (k = (2 * suffix ))) (PreH12 : (prefix = (n - suffix ))) (PreH13 : (0 <= prefix)) (PreH14 : (prefix <= n)) (PreH15 : (prefix <= i)) (PreH16 : (i <= n)) (PreH17 : (NoAInterval given_data prefix i )),
  (MatchedSuffixPrefix filtered_2 given_data (n - suffix ) 0 )
.

Definition solver_entail_wit_6_split_goal_2 :=
forall (given_data: (@list Z)) (i: Z) (prefix: Z) (suffix: Z) (filtered_2: (@list Z)) (k: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (0 <= k)) (PreH7 : (k <= n)) (PreH8 : (k = (Zlength (filtered_2)))) (PreH9 : (FilteredPrefix given_data n filtered_2 )) (PreH10 : (0 <= suffix)) (PreH11 : (k = (2 * suffix ))) (PreH12 : (prefix = (n - suffix ))) (PreH13 : (0 <= prefix)) (PreH14 : (prefix <= n)) (PreH15 : (prefix <= i)) (PreH16 : (i <= n)) (PreH17 : (NoAInterval given_data prefix i )),
  (NoAInterval given_data (n - suffix ) n )
.

Definition solver_entail_wit_6_split_goal_3 :=
forall (given_data: (@list Z)) (i: Z) (prefix: Z) (suffix: Z) (filtered_2: (@list Z)) (k: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (Zlength (given_data)))) -> ((97 <= (Znth j_2 given_data 0)) /\ ((Znth j_2 given_data 0) <= 122)))) (PreH6 : (0 <= k)) (PreH7 : (k <= n)) (PreH8 : (k = (Zlength (filtered_2)))) (PreH9 : (FilteredPrefix given_data n filtered_2 )) (PreH10 : (0 <= suffix)) (PreH11 : (k = (2 * suffix ))) (PreH12 : (prefix = (n - suffix ))) (PreH13 : (0 <= prefix)) (PreH14 : (prefix <= n)) (PreH15 : (prefix <= i)) (PreH16 : (i <= n)) (PreH17 : (NoAInterval given_data prefix i )),
  forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))
.

Definition solver_entail_wit_7 :=
(
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered_2: (@list Z)) (k: Z) (n: Z) (PreH1 : ((Znth i filtered_2 0) = (Znth (prefix + i ) (app (given_data) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (i < suffix)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= k)) (PreH8 : (k <= n)) (PreH9 : (k = (Zlength (filtered_2)))) (PreH10 : (FilteredPrefix given_data n filtered_2 )) (PreH11 : (0 <= suffix)) (PreH12 : (k = (2 * suffix ))) (PreH13 : (prefix = (n - suffix ))) (PreH14 : (0 <= prefix)) (PreH15 : (prefix <= n)) (PreH16 : (NoAInterval given_data prefix n )) (PreH17 : (0 <= i)) (PreH18 : (i <= suffix)) (PreH19 : (MatchedSuffixPrefix filtered_2 given_data prefix i )),
  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stripped" ) ) k filtered_2 )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  EX (filtered: (@list Z)),
  “ (n = (Zlength (given_data))) ”
  &&  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= n) ”
  &&  “ (k = (Zlength (filtered))) ”
  &&  “ (FilteredPrefix given_data n filtered ) ”
  &&  “ (0 <= suffix) ”
  &&  “ (k = (2 * suffix )) ”
  &&  “ (prefix = (n - suffix )) ”
  &&  “ (0 <= prefix) ”
  &&  “ (prefix <= n) ”
  &&  “ (NoAInterval given_data prefix n ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= suffix) ”
  &&  “ (MatchedSuffixPrefix filtered given_data prefix (i + 1 ) ) ”
  &&  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
) \/
(
forall (given_data: (@list Z)) (i: Z) (prefix: Z) (suffix: Z) (filtered_2: (@list Z)) (k: Z) (n: Z) (PreH1 : ((Znth i filtered_2 0) = (Znth (prefix + i ) (app (given_data) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (i < suffix)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= k)) (PreH8 : (k <= n)) (PreH9 : (k = (Zlength (filtered_2)))) (PreH10 : (FilteredPrefix given_data n filtered_2 )) (PreH11 : (0 <= suffix)) (PreH12 : (k = (2 * suffix ))) (PreH13 : (prefix = (n - suffix ))) (PreH14 : (0 <= prefix)) (PreH15 : (prefix <= n)) (PreH16 : (NoAInterval given_data prefix n )) (PreH17 : (0 <= i)) (PreH18 : (i <= suffix)) (PreH19 : (MatchedSuffixPrefix filtered_2 given_data prefix i )),
  TT && emp 
|--
  “ (MatchedSuffixPrefix filtered_2 given_data (n - suffix ) (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 :=
forall (given_data: (@list Z)) (i: Z) (prefix: Z) (suffix: Z) (filtered_2: (@list Z)) (k: Z) (n: Z) (PreH1 : ((Znth i filtered_2 0) = (Znth (prefix + i ) (app (given_data) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (i < suffix)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= k)) (PreH8 : (k <= n)) (PreH9 : (k = (Zlength (filtered_2)))) (PreH10 : (FilteredPrefix given_data n filtered_2 )) (PreH11 : (0 <= suffix)) (PreH12 : (k = (2 * suffix ))) (PreH13 : (prefix = (n - suffix ))) (PreH14 : (0 <= prefix)) (PreH15 : (prefix <= n)) (PreH16 : (NoAInterval given_data prefix n )) (PreH17 : (0 <= i)) (PreH18 : (i <= suffix)) (PreH19 : (MatchedSuffixPrefix filtered_2 given_data prefix i )),
  (MatchedSuffixPrefix filtered_2 given_data (n - suffix ) (i + 1 ) )
.

Definition solver_return_wit_1 :=
(
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (filtered_2: (@list Z)) (PreH1 : (k = (Zlength (filtered_2)))) (PreH2 : (i >= suffix)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= k)) (PreH8 : (k <= n)) (PreH9 : (k = (Zlength (filtered)))) (PreH10 : (FilteredPrefix given_data n filtered )) (PreH11 : (0 <= suffix)) (PreH12 : (k = (2 * suffix ))) (PreH13 : (prefix = (n - suffix ))) (PreH14 : (0 <= prefix)) (PreH15 : (prefix <= n)) (PreH16 : (NoAInterval given_data prefix n )) (PreH17 : (0 <= i)) (PreH18 : (i <= suffix)) (PreH19 : (MatchedSuffixPrefix filtered given_data prefix i )),
  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (replace_Znth (prefix) (0) ((app (given_data) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
|--
  EX (result: (@list Z)),
  “ (1 = 1) ”
  &&  “ (Spec given_data (Some (result)) ) ”
  &&  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (result)) + 1 ) (app (result) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (result)) + 1 ) 100005 )
) \/
(
forall (given_data: (@list Z)) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (filtered_2: (@list Z)) (PreH1 : (k = (Zlength (filtered_2)))) (PreH2 : (i >= suffix)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= k)) (PreH8 : (k <= n)) (PreH9 : (k = (Zlength (filtered)))) (PreH10 : (FilteredPrefix given_data n filtered )) (PreH11 : (0 <= suffix)) (PreH12 : (k = (2 * suffix ))) (PreH13 : (prefix = (n - suffix ))) (PreH14 : (0 <= prefix)) (PreH15 : (prefix <= n)) (PreH16 : (NoAInterval given_data prefix n )) (PreH17 : (0 <= i)) (PreH18 : (i <= suffix)) (PreH19 : (MatchedSuffixPrefix filtered given_data prefix i )),
  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (replace_Znth (prefix) (0) ((app (given_data) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
|--
  EX (result: (@list Z)),
  “ (Spec given_data (Some (result)) ) ”
  &&  (CharArray.full out_pre ((Zlength (result)) + 1 ) (app (result) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (result)) + 1 ) 100005 )
).

Definition solver_return_wit_2 :=
(
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (filtered_2: (@list Z)) (PreH1 : (k = (Zlength (filtered_2)))) (PreH2 : ((Znth i filtered 0) <> (Znth (prefix + i ) (app (given_data) ((cons (0) ((@nil Z))))) 0))) (PreH3 : (i < suffix)) (PreH4 : (n = (Zlength (given_data)))) (PreH5 : (1 <= (Zlength (given_data)))) (PreH6 : ((Zlength (given_data)) <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n)) (PreH10 : (k = (Zlength (filtered)))) (PreH11 : (FilteredPrefix given_data n filtered )) (PreH12 : (0 <= suffix)) (PreH13 : (k = (2 * suffix ))) (PreH14 : (prefix = (n - suffix ))) (PreH15 : (0 <= prefix)) (PreH16 : (prefix <= n)) (PreH17 : (NoAInterval given_data prefix n )) (PreH18 : (0 <= i)) (PreH19 : (i <= suffix)) (PreH20 : (MatchedSuffixPrefix filtered given_data prefix i )),
  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
|--
  “ (0 = 0) ”
  &&  “ (Spec given_data None ) ”
  &&  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
) \/
(
forall (given_data: (@list Z)) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (filtered_2: (@list Z)) (PreH1 : (k = (Zlength (filtered_2)))) (PreH2 : ((Znth i filtered 0) <> (Znth (prefix + i ) (app (given_data) ((cons (0) ((@nil Z))))) 0))) (PreH3 : (i < suffix)) (PreH4 : (n = (Zlength (given_data)))) (PreH5 : (1 <= (Zlength (given_data)))) (PreH6 : ((Zlength (given_data)) <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n)) (PreH10 : (k = (Zlength (filtered)))) (PreH11 : (FilteredPrefix given_data n filtered )) (PreH12 : (0 <= suffix)) (PreH13 : (k = (2 * suffix ))) (PreH14 : (prefix = (n - suffix ))) (PreH15 : (0 <= prefix)) (PreH16 : (prefix <= n)) (PreH17 : (NoAInterval given_data prefix n )) (PreH18 : (0 <= i)) (PreH19 : (i <= suffix)) (PreH20 : (MatchedSuffixPrefix filtered given_data prefix i )),
  TT && emp 
|--
  “ (Spec given_data None ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 :=
forall (given_data: (@list Z)) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (filtered_2: (@list Z)) (PreH1 : (k = (Zlength (filtered_2)))) (PreH2 : ((Znth i filtered 0) <> (Znth (prefix + i ) (app (given_data) ((cons (0) ((@nil Z))))) 0))) (PreH3 : (i < suffix)) (PreH4 : (n = (Zlength (given_data)))) (PreH5 : (1 <= (Zlength (given_data)))) (PreH6 : ((Zlength (given_data)) <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n)) (PreH10 : (k = (Zlength (filtered)))) (PreH11 : (FilteredPrefix given_data n filtered )) (PreH12 : (0 <= suffix)) (PreH13 : (k = (2 * suffix ))) (PreH14 : (prefix = (n - suffix ))) (PreH15 : (0 <= prefix)) (PreH16 : (prefix <= n)) (PreH17 : (NoAInterval given_data prefix n )) (PreH18 : (0 <= i)) (PreH19 : (i <= suffix)) (PreH20 : (MatchedSuffixPrefix filtered given_data prefix i )),
  (Spec given_data None )
.

Definition solver_return_wit_3 :=
(
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (filtered_2: (@list Z)) (PreH1 : (k = (Zlength (filtered_2)))) (PreH2 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) = 97)) (PreH3 : (i < n)) (PreH4 : (n = (Zlength (given_data)))) (PreH5 : (1 <= (Zlength (given_data)))) (PreH6 : ((Zlength (given_data)) <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n)) (PreH10 : (k = (Zlength (filtered)))) (PreH11 : (FilteredPrefix given_data n filtered )) (PreH12 : (0 <= suffix)) (PreH13 : (k = (2 * suffix ))) (PreH14 : (prefix = (n - suffix ))) (PreH15 : (0 <= prefix)) (PreH16 : (prefix <= n)) (PreH17 : (prefix <= i)) (PreH18 : (i <= n)) (PreH19 : (NoAInterval given_data prefix i )),
  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
|--
  “ (0 = 0) ”
  &&  “ (Spec given_data None ) ”
  &&  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
) \/
(
forall (given_data: (@list Z)) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (filtered_2: (@list Z)) (PreH1 : (k = (Zlength (filtered_2)))) (PreH2 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) = 97)) (PreH3 : (i < n)) (PreH4 : (n = (Zlength (given_data)))) (PreH5 : (1 <= (Zlength (given_data)))) (PreH6 : ((Zlength (given_data)) <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n)) (PreH10 : (k = (Zlength (filtered)))) (PreH11 : (FilteredPrefix given_data n filtered )) (PreH12 : (0 <= suffix)) (PreH13 : (k = (2 * suffix ))) (PreH14 : (prefix = (n - suffix ))) (PreH15 : (0 <= prefix)) (PreH16 : (prefix <= n)) (PreH17 : (prefix <= i)) (PreH18 : (i <= n)) (PreH19 : (NoAInterval given_data prefix i )),
  TT && emp 
|--
  “ (Spec given_data None ) ”
  &&  emp
).

Definition solver_return_wit_3_split_goal_1 :=
forall (given_data: (@list Z)) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (filtered_2: (@list Z)) (PreH1 : (k = (Zlength (filtered_2)))) (PreH2 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) = 97)) (PreH3 : (i < n)) (PreH4 : (n = (Zlength (given_data)))) (PreH5 : (1 <= (Zlength (given_data)))) (PreH6 : ((Zlength (given_data)) <= 100000)) (PreH7 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n)) (PreH10 : (k = (Zlength (filtered)))) (PreH11 : (FilteredPrefix given_data n filtered )) (PreH12 : (0 <= suffix)) (PreH13 : (k = (2 * suffix ))) (PreH14 : (prefix = (n - suffix ))) (PreH15 : (0 <= prefix)) (PreH16 : (prefix <= n)) (PreH17 : (prefix <= i)) (PreH18 : (i <= n)) (PreH19 : (NoAInterval given_data prefix i )),
  (Spec given_data None )
.

Definition solver_return_wit_4 :=
(
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (filtered: (@list Z)) (k: Z) (i: Z) (n: Z) (filtered_2: (@list Z)) (PreH1 : (k = (Zlength (filtered_2)))) (PreH2 : (i >= n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered)))) (PreH12 : (FilteredPrefix given_data i filtered )) (PreH13 : ((Z.land k 1) <> 0)),
  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
|--
  “ (0 = 0) ”
  &&  “ (Spec given_data None ) ”
  &&  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
) \/
(
forall (given_data: (@list Z)) (filtered: (@list Z)) (k: Z) (i: Z) (n: Z) (filtered_2: (@list Z)) (PreH1 : (k = (Zlength (filtered_2)))) (PreH2 : (i >= n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered)))) (PreH12 : (FilteredPrefix given_data i filtered )) (PreH13 : ((Z.land k 1) <> 0)),
  TT && emp 
|--
  “ (Spec given_data None ) ”
  &&  emp
).

Definition solver_return_wit_4_split_goal_1 :=
forall (given_data: (@list Z)) (filtered: (@list Z)) (k: Z) (i: Z) (n: Z) (filtered_2: (@list Z)) (PreH1 : (k = (Zlength (filtered_2)))) (PreH2 : (i >= n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered)))) (PreH12 : (FilteredPrefix given_data i filtered )) (PreH13 : ((Z.land k 1) <> 0)),
  (Spec given_data None )
.

Definition solver_partial_solve_wit_1_pure :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (PreH1 : (1 <= (Zlength (given_data)))) (PreH2 : ((Zlength (given_data)) <= 100000)) (PreH3 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH4 : (valid_string given_data )) (PreH5 : ((string_length (given_data)) = (Zlength (given_data)))) (PreH6 : ((string_length (given_data)) < INT_MAX)),
  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (store_string given_pre given_data )
  **  (CharArray.undef_full out_pre ((string_length (given_data)) + 1 ) )
  **  (CharArray.undef_seg out_pre ((string_length (given_data)) + 1 ) 100005 )
  **  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
|--
  “ (valid_string given_data ) ”
  &&  “ ((string_length (given_data)) < INT_MAX) ”
.

Definition solver_partial_solve_wit_1_aux :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (PreH1 : (1 <= (Zlength (given_data)))) (PreH2 : ((Zlength (given_data)) <= 100000)) (PreH3 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH4 : (valid_string given_data )) (PreH5 : ((string_length (given_data)) = (Zlength (given_data)))) (PreH6 : ((string_length (given_data)) < INT_MAX)),
  (store_string given_pre given_data )
  **  (CharArray.undef_full out_pre ((string_length (given_data)) + 1 ) )
  **  (CharArray.undef_seg out_pre ((string_length (given_data)) + 1 ) 100005 )
  **  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
|--
  “ (valid_string given_data ) ”
  &&  “ ((string_length (given_data)) < INT_MAX) ”
  &&  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (valid_string given_data ) ”
  &&  “ ((string_length (given_data)) = (Zlength (given_data))) ”
  &&  “ ((string_length (given_data)) < INT_MAX) ”
  &&  (CharArray.undef_full out_pre ((string_length (given_data)) + 1 ) )
  **  (store_string given_pre given_data )
  **  (CharArray.undef_seg out_pre ((string_length (given_data)) + 1 ) 100005 )
  **  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2_pure :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (retval: Z) (PreH1 : (retval = out_pre)) (PreH2 : (1 <= (Zlength (given_data)))) (PreH3 : ((Zlength (given_data)) <= 100000)) (PreH4 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH5 : (valid_string given_data )) (PreH6 : ((string_length (given_data)) = (Zlength (given_data)))) (PreH7 : ((string_length (given_data)) < INT_MAX)),
  ((( &( "n" ) )) # Int  |->_)
  **  (store_string out_pre given_data )
  **  (store_string given_pre given_data )
  **  ((( &( "given" ) )) # Ptr  |-> given_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.undef_seg out_pre ((string_length (given_data)) + 1 ) 100005 )
  **  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
|--
  “ (valid_string given_data ) ”
  &&  “ ((string_length (given_data)) < INT_MAX) ”
.

Definition solver_partial_solve_wit_2_aux :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (retval: Z) (PreH1 : (retval = out_pre)) (PreH2 : (1 <= (Zlength (given_data)))) (PreH3 : ((Zlength (given_data)) <= 100000)) (PreH4 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH5 : (valid_string given_data )) (PreH6 : ((string_length (given_data)) = (Zlength (given_data)))) (PreH7 : ((string_length (given_data)) < INT_MAX)),
  (store_string out_pre given_data )
  **  (store_string given_pre given_data )
  **  (CharArray.undef_seg out_pre ((string_length (given_data)) + 1 ) 100005 )
  **  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
|--
  “ (valid_string given_data ) ”
  &&  “ ((string_length (given_data)) < INT_MAX) ”
  &&  “ (retval = out_pre) ”
  &&  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (valid_string given_data ) ”
  &&  “ ((string_length (given_data)) = (Zlength (given_data))) ”
  &&  “ ((string_length (given_data)) < INT_MAX) ”
  &&  (store_string out_pre given_data )
  **  (CharArray.full given_pre ((string_length (given_data)) + 1 ) (c_string (given_data)) )
  **  (CharArray.undef_seg out_pre ((string_length (given_data)) + 1 ) 100005 )
  **  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (filtered: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered)))) (PreH11 : (FilteredPrefix given_data i filtered )),
  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ (i < n) ”
  &&  “ (n = (Zlength (given_data))) ”
  &&  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= i) ”
  &&  “ (k = (Zlength (filtered))) ”
  &&  “ (FilteredPrefix given_data i filtered ) ”
  &&  (((out_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i out_pre i 0 ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
.

Definition solver_partial_solve_wit_4 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (filtered: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) <> 97)) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered)))) (PreH12 : (FilteredPrefix given_data i filtered )),
  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) <> 97) ”
  &&  “ (i < n) ”
  &&  “ (n = (Zlength (given_data))) ”
  &&  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= i) ”
  &&  “ (k = (Zlength (filtered))) ”
  &&  “ (FilteredPrefix given_data i filtered ) ”
  &&  (((out_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i out_pre i 0 ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
.

Definition solver_partial_solve_wit_5 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (filtered: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) <> 97)) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered)))) (PreH12 : (FilteredPrefix given_data i filtered )),
  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) <> 97) ”
  &&  “ (i < n) ”
  &&  “ (n = (Zlength (given_data))) ”
  &&  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= i) ”
  &&  “ (k = (Zlength (filtered))) ”
  &&  “ (FilteredPrefix given_data i filtered ) ”
  &&  (((( &( "stripped" ) ) + (k * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg ( &( "stripped" ) ) (k + 1 ) 100005 )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
.

Definition solver_partial_solve_wit_6 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (filtered: (@list Z)) (k: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered)))) (PreH11 : (FilteredPrefix given_data i filtered )) (PreH12 : ((Z.land k 1) <> 0)),
  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ (i >= n) ”
  &&  “ (n = (Zlength (given_data))) ”
  &&  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= i) ”
  &&  “ (k = (Zlength (filtered))) ”
  &&  “ (FilteredPrefix given_data i filtered ) ”
  &&  “ ((Z.land k 1) <> 0) ”
  &&  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
.

Definition solver_partial_solve_wit_7 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (0 <= k)) (PreH7 : (k <= n)) (PreH8 : (k = (Zlength (filtered)))) (PreH9 : (FilteredPrefix given_data n filtered )) (PreH10 : (0 <= suffix)) (PreH11 : (k = (2 * suffix ))) (PreH12 : (prefix = (n - suffix ))) (PreH13 : (0 <= prefix)) (PreH14 : (prefix <= n)) (PreH15 : (prefix <= i)) (PreH16 : (i <= n)) (PreH17 : (NoAInterval given_data prefix i )),
  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ (i < n) ”
  &&  “ (n = (Zlength (given_data))) ”
  &&  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= n) ”
  &&  “ (k = (Zlength (filtered))) ”
  &&  “ (FilteredPrefix given_data n filtered ) ”
  &&  “ (0 <= suffix) ”
  &&  “ (k = (2 * suffix )) ”
  &&  “ (prefix = (n - suffix )) ”
  &&  “ (0 <= prefix) ”
  &&  “ (prefix <= n) ”
  &&  “ (prefix <= i) ”
  &&  “ (i <= n) ”
  &&  “ (NoAInterval given_data prefix i ) ”
  &&  (((out_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i out_pre i 0 ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
.

Definition solver_partial_solve_wit_8 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (PreH1 : ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) = 97)) (PreH2 : (i < n)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= k)) (PreH8 : (k <= n)) (PreH9 : (k = (Zlength (filtered)))) (PreH10 : (FilteredPrefix given_data n filtered )) (PreH11 : (0 <= suffix)) (PreH12 : (k = (2 * suffix ))) (PreH13 : (prefix = (n - suffix ))) (PreH14 : (0 <= prefix)) (PreH15 : (prefix <= n)) (PreH16 : (prefix <= i)) (PreH17 : (i <= n)) (PreH18 : (NoAInterval given_data prefix i )),
  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ ((Znth i (app (given_data) ((cons (0) ((@nil Z))))) 0) = 97) ”
  &&  “ (i < n) ”
  &&  “ (n = (Zlength (given_data))) ”
  &&  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= n) ”
  &&  “ (k = (Zlength (filtered))) ”
  &&  “ (FilteredPrefix given_data n filtered ) ”
  &&  “ (0 <= suffix) ”
  &&  “ (k = (2 * suffix )) ”
  &&  “ (prefix = (n - suffix )) ”
  &&  “ (0 <= prefix) ”
  &&  “ (prefix <= n) ”
  &&  “ (prefix <= i) ”
  &&  “ (i <= n) ”
  &&  “ (NoAInterval given_data prefix i ) ”
  &&  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
.

Definition solver_partial_solve_wit_9 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (PreH1 : (i < suffix)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (0 <= k)) (PreH7 : (k <= n)) (PreH8 : (k = (Zlength (filtered)))) (PreH9 : (FilteredPrefix given_data n filtered )) (PreH10 : (0 <= suffix)) (PreH11 : (k = (2 * suffix ))) (PreH12 : (prefix = (n - suffix ))) (PreH13 : (0 <= prefix)) (PreH14 : (prefix <= n)) (PreH15 : (NoAInterval given_data prefix n )) (PreH16 : (0 <= i)) (PreH17 : (i <= suffix)) (PreH18 : (MatchedSuffixPrefix filtered given_data prefix i )),
  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ (i < suffix) ”
  &&  “ (n = (Zlength (given_data))) ”
  &&  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= n) ”
  &&  “ (k = (Zlength (filtered))) ”
  &&  “ (FilteredPrefix given_data n filtered ) ”
  &&  “ (0 <= suffix) ”
  &&  “ (k = (2 * suffix )) ”
  &&  “ (prefix = (n - suffix )) ”
  &&  “ (0 <= prefix) ”
  &&  “ (prefix <= n) ”
  &&  “ (NoAInterval given_data prefix n ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= suffix) ”
  &&  “ (MatchedSuffixPrefix filtered given_data prefix i ) ”
  &&  (((( &( "stripped" ) ) + (i * sizeof(CHAR)))) # Char  |-> (Znth i filtered 0))
  **  (CharArray.missing_i ( &( "stripped" ) ) i 0 k filtered )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
.

Definition solver_partial_solve_wit_10 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (PreH1 : (i < suffix)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (0 <= k)) (PreH7 : (k <= n)) (PreH8 : (k = (Zlength (filtered)))) (PreH9 : (FilteredPrefix given_data n filtered )) (PreH10 : (0 <= suffix)) (PreH11 : (k = (2 * suffix ))) (PreH12 : (prefix = (n - suffix ))) (PreH13 : (0 <= prefix)) (PreH14 : (prefix <= n)) (PreH15 : (NoAInterval given_data prefix n )) (PreH16 : (0 <= i)) (PreH17 : (i <= suffix)) (PreH18 : (MatchedSuffixPrefix filtered given_data prefix i )),
  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ (i < suffix) ”
  &&  “ (n = (Zlength (given_data))) ”
  &&  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= n) ”
  &&  “ (k = (Zlength (filtered))) ”
  &&  “ (FilteredPrefix given_data n filtered ) ”
  &&  “ (0 <= suffix) ”
  &&  “ (k = (2 * suffix )) ”
  &&  “ (prefix = (n - suffix )) ”
  &&  “ (0 <= prefix) ”
  &&  “ (prefix <= n) ”
  &&  “ (NoAInterval given_data prefix n ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= suffix) ”
  &&  “ (MatchedSuffixPrefix filtered given_data prefix i ) ”
  &&  (((out_pre + ((prefix + i ) * sizeof(CHAR)))) # Char  |-> (Znth (prefix + i ) (app (given_data) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i out_pre (prefix + i ) 0 ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
.

Definition solver_partial_solve_wit_11 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (PreH1 : ((Znth i filtered 0) <> (Znth (prefix + i ) (app (given_data) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (i < suffix)) (PreH3 : (n = (Zlength (given_data)))) (PreH4 : (1 <= (Zlength (given_data)))) (PreH5 : ((Zlength (given_data)) <= 100000)) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH7 : (0 <= k)) (PreH8 : (k <= n)) (PreH9 : (k = (Zlength (filtered)))) (PreH10 : (FilteredPrefix given_data n filtered )) (PreH11 : (0 <= suffix)) (PreH12 : (k = (2 * suffix ))) (PreH13 : (prefix = (n - suffix ))) (PreH14 : (0 <= prefix)) (PreH15 : (prefix <= n)) (PreH16 : (NoAInterval given_data prefix n )) (PreH17 : (0 <= i)) (PreH18 : (i <= suffix)) (PreH19 : (MatchedSuffixPrefix filtered given_data prefix i )),
  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ ((Znth i filtered 0) <> (Znth (prefix + i ) (app (given_data) ((cons (0) ((@nil Z))))) 0)) ”
  &&  “ (i < suffix) ”
  &&  “ (n = (Zlength (given_data))) ”
  &&  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= n) ”
  &&  “ (k = (Zlength (filtered))) ”
  &&  “ (FilteredPrefix given_data n filtered ) ”
  &&  “ (0 <= suffix) ”
  &&  “ (k = (2 * suffix )) ”
  &&  “ (prefix = (n - suffix )) ”
  &&  “ (0 <= prefix) ”
  &&  “ (prefix <= n) ”
  &&  “ (NoAInterval given_data prefix n ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= suffix) ”
  &&  “ (MatchedSuffixPrefix filtered given_data prefix i ) ”
  &&  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
.

Definition solver_partial_solve_wit_12 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (PreH1 : (i >= suffix)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (0 <= k)) (PreH7 : (k <= n)) (PreH8 : (k = (Zlength (filtered)))) (PreH9 : (FilteredPrefix given_data n filtered )) (PreH10 : (0 <= suffix)) (PreH11 : (k = (2 * suffix ))) (PreH12 : (prefix = (n - suffix ))) (PreH13 : (0 <= prefix)) (PreH14 : (prefix <= n)) (PreH15 : (NoAInterval given_data prefix n )) (PreH16 : (0 <= i)) (PreH17 : (i <= suffix)) (PreH18 : (MatchedSuffixPrefix filtered given_data prefix i )),
  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ (i >= suffix) ”
  &&  “ (n = (Zlength (given_data))) ”
  &&  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= n) ”
  &&  “ (k = (Zlength (filtered))) ”
  &&  “ (FilteredPrefix given_data n filtered ) ”
  &&  “ (0 <= suffix) ”
  &&  “ (k = (2 * suffix )) ”
  &&  “ (prefix = (n - suffix )) ”
  &&  “ (0 <= prefix) ”
  &&  “ (prefix <= n) ”
  &&  “ (NoAInterval given_data prefix n ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= suffix) ”
  &&  “ (MatchedSuffixPrefix filtered given_data prefix i ) ”
  &&  (((out_pre + (prefix * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i out_pre prefix 0 ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
.

Definition solver_partial_solve_wit_13 :=
forall (given_data: (@list Z)) (given_pre: Z) (out_pre: Z) (i: Z) (prefix: Z) (suffix: Z) (filtered: (@list Z)) (k: Z) (n: Z) (PreH1 : (i >= suffix)) (PreH2 : (n = (Zlength (given_data)))) (PreH3 : (1 <= (Zlength (given_data)))) (PreH4 : ((Zlength (given_data)) <= 100000)) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122)))) (PreH6 : (0 <= k)) (PreH7 : (k <= n)) (PreH8 : (k = (Zlength (filtered)))) (PreH9 : (FilteredPrefix given_data n filtered )) (PreH10 : (0 <= suffix)) (PreH11 : (k = (2 * suffix ))) (PreH12 : (prefix = (n - suffix ))) (PreH13 : (0 <= prefix)) (PreH14 : (prefix <= n)) (PreH15 : (NoAInterval given_data prefix n )) (PreH16 : (0 <= i)) (PreH17 : (i <= suffix)) (PreH18 : (MatchedSuffixPrefix filtered given_data prefix i )),
  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (replace_Znth (prefix) (0) ((app (given_data) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
  **  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  “ (i >= suffix) ”
  &&  “ (n = (Zlength (given_data))) ”
  &&  “ (1 <= (Zlength (given_data))) ”
  &&  “ ((Zlength (given_data)) <= 100000) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (Zlength (given_data)))) -> ((97 <= (Znth j given_data 0)) /\ ((Znth j given_data 0) <= 122))) ”
  &&  “ (0 <= k) ”
  &&  “ (k <= n) ”
  &&  “ (k = (Zlength (filtered))) ”
  &&  “ (FilteredPrefix given_data n filtered ) ”
  &&  “ (0 <= suffix) ”
  &&  “ (k = (2 * suffix )) ”
  &&  “ (prefix = (n - suffix )) ”
  &&  “ (0 <= prefix) ”
  &&  “ (prefix <= n) ”
  &&  “ (NoAInterval given_data prefix n ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= suffix) ”
  &&  “ (MatchedSuffixPrefix filtered given_data prefix i ) ”
  &&  (CharArray.full ( &( "stripped" ) ) k filtered )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
  **  (CharArray.full out_pre ((Zlength (given_data)) + 1 ) (replace_Znth (prefix) (0) ((app (given_data) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full given_pre ((Zlength (given_data)) + 1 ) (app (given_data) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (given_data)) + 1 ) 100005 )
.

Definition solver_which_implies_wit_1 :=
(
forall (filtered_2: (@list Z)) (k: Z),
  (CharArray.full ( &( "stripped" ) ) k filtered_2 )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  EX (filtered: (@list Z)),
  “ (k = (Zlength (filtered))) ”
  &&  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
) \/
(
forall (filtered_2: (@list Z)) (k: Z),
  (CharArray.full ( &( "stripped" ) ) k filtered_2 )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  EX (filtered: (@list Z)),
  “ (k = (Zlength (filtered))) ”
  &&  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
).

Definition solver_which_implies_wit_2 :=
(
forall (filtered_2: (@list Z)) (k: Z),
  (CharArray.full ( &( "stripped" ) ) k filtered_2 )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  EX (filtered: (@list Z)),
  “ (k = (Zlength (filtered))) ”
  &&  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
) \/
(
forall (filtered_2: (@list Z)) (k: Z),
  (CharArray.full ( &( "stripped" ) ) k filtered_2 )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  EX (filtered: (@list Z)),
  “ (k = (Zlength (filtered))) ”
  &&  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
).

Definition solver_which_implies_wit_3 :=
(
forall (filtered_2: (@list Z)) (k: Z),
  (CharArray.full ( &( "stripped" ) ) k filtered_2 )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  EX (filtered: (@list Z)),
  “ (k = (Zlength (filtered))) ”
  &&  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
) \/
(
forall (filtered_2: (@list Z)) (k: Z),
  (CharArray.full ( &( "stripped" ) ) k filtered_2 )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  EX (filtered: (@list Z)),
  “ (k = (Zlength (filtered))) ”
  &&  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
).

Definition solver_which_implies_wit_4 :=
(
forall (filtered_2: (@list Z)) (k: Z),
  (CharArray.full ( &( "stripped" ) ) k filtered_2 )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  EX (filtered: (@list Z)),
  “ (k = (Zlength (filtered))) ”
  &&  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
) \/
(
forall (filtered_2: (@list Z)) (k: Z),
  (CharArray.full ( &( "stripped" ) ) k filtered_2 )
  **  (CharArray.undef_seg ( &( "stripped" ) ) k 100005 )
|--
  EX (filtered: (@list Z)),
  “ (k = (Zlength (filtered))) ”
  &&  (CharArray.undef_full ( &( "stripped" ) ) 100005 )
).

Module Type VC_Correct.

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
Axiom proof_of_solver_safety_wit_20 : solver_safety_wit_20.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Axiom proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_return_wit_4 : solver_return_wit_4.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
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
Axiom proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.
Axiom proof_of_solver_which_implies_wit_2 : solver_which_implies_wit_2.
Axiom proof_of_solver_which_implies_wit_3 : solver_which_implies_wit_3.
Axiom proof_of_solver_which_implies_wit_4 : solver_which_implies_wit_4.

End VC_Correct.
