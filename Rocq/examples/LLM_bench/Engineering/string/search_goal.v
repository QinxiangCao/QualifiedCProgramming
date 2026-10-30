From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Local Open Scope sac.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function memchr -----*)

Definition memchr_safety_wit_1 :=
forall (bytes: (@list Z)) (s_pre: Z) (c_pre: Z) (n_pre: Z) (PreH1 : (all_ascii bytes )) (PreH2 : ((Zlength (bytes)) = n_pre)) (PreH3 : (0 <= c_pre)) (PreH4 : (c_pre <= 127)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre n_pre bytes )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memchr_safety_wit_2 :=
forall (bytes: (@list Z)) (s_pre: Z) (c_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((Znth i bytes 0) <> c_pre)) (PreH2 : (i < n_pre)) (PreH3 : (all_ascii bytes )) (PreH4 : ((Zlength (bytes)) = n_pre)) (PreH5 : (0 <= c_pre)) (PreH6 : (c_pre <= 127)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre))),
  (CharArray.full s_pre n_pre bytes )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition memchr_safety_wit_3 :=
forall (bytes: (@list Z)) (s_pre: Z) (c_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre))),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre n_pre bytes )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memchr_entail_wit_1 :=
(
forall (bytes: (@list Z)) (s_pre: Z) (c_pre: Z) (n_pre: Z) (PreH1 : (all_ascii bytes )) (PreH2 : ((Zlength (bytes)) = n_pre)) (PreH3 : (0 <= c_pre)) (PreH4 : (c_pre <= 127)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)),
  (CharArray.full s_pre n_pre bytes )
|--
  “ (all_ascii bytes ) ”
  &&  “ ((Zlength (bytes)) = n_pre) ”
  &&  “ (0 <= c_pre) ”
  &&  “ (c_pre <= 127) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre < INT_MAX) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < 0)) -> ((Znth (k) (bytes) (0)) <> c_pre)) ”
  &&  (CharArray.full s_pre n_pre bytes )
) \/
(
forall (bytes: (@list Z)) (c_pre: Z) (n_pre: Z) (PreH1 : (all_ascii bytes )) (PreH2 : ((Zlength (bytes)) = n_pre)) (PreH3 : (0 <= c_pre)) (PreH4 : (c_pre <= 127)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)),
  TT && emp 
|--
  “ forall (k: Z), (((0 <= k) /\ (k < 0)) -> ((Znth (k) (bytes) (0)) <> c_pre)) ”
  &&  emp
).

Definition memchr_entail_wit_1_split_goal_1 :=
forall (bytes: (@list Z)) (c_pre: Z) (n_pre: Z) (PreH1 : (all_ascii bytes )) (PreH2 : ((Zlength (bytes)) = n_pre)) (PreH3 : (0 <= c_pre)) (PreH4 : (c_pre <= 127)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)),
  forall (k: Z), (((0 <= k) /\ (k < 0)) -> ((Znth (k) (bytes) (0)) <> c_pre))
.

Definition memchr_entail_wit_2 :=
forall (bytes: (@list Z)) (s_pre: Z) (c_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((Znth i bytes 0) <> c_pre)) (PreH2 : (i < n_pre)) (PreH3 : (all_ascii bytes )) (PreH4 : ((Zlength (bytes)) = n_pre)) (PreH5 : (0 <= c_pre)) (PreH6 : (c_pre <= 127)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre))),
  (CharArray.full s_pre n_pre bytes )
|--
  “ (all_ascii bytes ) ”
  &&  “ ((Zlength (bytes)) = n_pre) ”
  &&  “ (0 <= c_pre) ”
  &&  “ (c_pre <= 127) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre < INT_MAX) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (bytes) (0)) <> c_pre)) ”
  &&  (CharArray.full s_pre n_pre bytes )
.

Definition memchr_return_wit_1 :=
(
forall (bytes: (@list Z)) (s_pre: Z) (c_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre))),
  (CharArray.full s_pre n_pre bytes )
|--
  “ (memchr_result bytes c_pre n_pre 0 s_pre ) ”
  &&  (CharArray.full s_pre n_pre bytes )
) \/
(
forall (bytes: (@list Z)) (s_pre: Z) (c_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre))),
  TT && emp 
|--
  “ (memchr_result bytes c_pre n_pre 0 s_pre ) ”
  &&  emp
).

Definition memchr_return_wit_1_split_goal_1 :=
forall (bytes: (@list Z)) (s_pre: Z) (c_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre))),
  (memchr_result bytes c_pre n_pre 0 s_pre )
.

Definition memchr_return_wit_2 :=
(
forall (bytes: (@list Z)) (s_pre: Z) (c_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((Znth i bytes 0) = c_pre)) (PreH2 : (i < n_pre)) (PreH3 : (all_ascii bytes )) (PreH4 : ((Zlength (bytes)) = n_pre)) (PreH5 : (0 <= c_pre)) (PreH6 : (c_pre <= 127)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre))),
  (CharArray.full s_pre n_pre bytes )
|--
  “ (memchr_result bytes c_pre n_pre (s_pre + (i * sizeof(CHAR))) s_pre ) ”
  &&  (CharArray.full s_pre n_pre bytes )
) \/
(
forall (bytes: (@list Z)) (s_pre: Z) (c_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((Znth i bytes 0) = c_pre)) (PreH2 : (i < n_pre)) (PreH3 : (all_ascii bytes )) (PreH4 : ((Zlength (bytes)) = n_pre)) (PreH5 : (0 <= c_pre)) (PreH6 : (c_pre <= 127)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre))),
  TT && emp 
|--
  “ (memchr_result bytes c_pre n_pre (s_pre + (i * sizeof(CHAR))) s_pre ) ”
  &&  emp
).

Definition memchr_return_wit_2_split_goal_1 :=
forall (bytes: (@list Z)) (s_pre: Z) (c_pre: Z) (n_pre: Z) (i: Z) (PreH1 : ((Znth i bytes 0) = c_pre)) (PreH2 : (i < n_pre)) (PreH3 : (all_ascii bytes )) (PreH4 : ((Zlength (bytes)) = n_pre)) (PreH5 : (0 <= c_pre)) (PreH6 : (c_pre <= 127)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre))),
  (memchr_result bytes c_pre n_pre (s_pre + (i * sizeof(CHAR))) s_pre )
.

Definition memchr_partial_solve_wit_1 :=
forall (bytes: (@list Z)) (s_pre: Z) (c_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre))),
  (CharArray.full s_pre n_pre bytes )
|--
  “ (i < n_pre) ”
  &&  “ (all_ascii bytes ) ”
  &&  “ ((Zlength (bytes)) = n_pre) ”
  &&  “ (0 <= c_pre) ”
  &&  “ (c_pre <= 127) ”
  &&  “ (0 <= n_pre) ”
  &&  “ (n_pre < INT_MAX) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre)) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i bytes 0))
  **  (CharArray.missing_i s_pre i 0 n_pre bytes )
.

(*----- Function strchr -----*)

Definition strchr_safety_wit_1 :=
forall (str: (@list Z)) (s_pre: Z) (c_pre: Z) (PreH1 : (valid_string str )) (PreH2 : (0 <= c_pre)) (PreH3 : (c_pre <= 127)) (PreH4 : ((string_length (str)) < INT_MAX)),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  (store_string s_pre str )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strchr_safety_wit_2 :=
forall (str: (@list Z)) (s_pre: Z) (c_pre: Z) (i: Z) (PreH1 : (valid_string str )) (PreH2 : (0 <= c_pre)) (PreH3 : (c_pre <= 127)) (PreH4 : ((string_length (str)) < INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= (string_length (str)))) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre))),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  (store_string s_pre str )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strchr_safety_wit_3 :=
forall (str: (@list Z)) (s_pre: Z) (c_pre: Z) (i: Z) (PreH1 : ((Znth i (c_string (str)) 0) <> c_pre)) (PreH2 : ((Znth i (c_string (str)) 0) <> 0)) (PreH3 : (valid_string str )) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : ((string_length (str)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre))),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  (store_string s_pre str )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition strchr_safety_wit_4 :=
forall (str: (@list Z)) (s_pre: Z) (c_pre: Z) (i: Z) (PreH1 : ((Znth i (c_string (str)) 0) = 0)) (PreH2 : (valid_string str )) (PreH3 : (0 <= c_pre)) (PreH4 : (c_pre <= 127)) (PreH5 : ((string_length (str)) < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= (string_length (str)))) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre))),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  (store_string s_pre str )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strchr_safety_wit_5 :=
forall (str: (@list Z)) (s_pre: Z) (c_pre: Z) (i: Z) (PreH1 : (c_pre <> 0)) (PreH2 : ((Znth i (c_string (str)) 0) = 0)) (PreH3 : (valid_string str )) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : ((string_length (str)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre))),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  (store_string s_pre str )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strchr_entail_wit_1 :=
(
forall (str: (@list Z)) (s_pre: Z) (c_pre: Z) (PreH1 : (valid_string str )) (PreH2 : (0 <= c_pre)) (PreH3 : (c_pre <= 127)) (PreH4 : ((string_length (str)) < INT_MAX)),
  (store_string s_pre str )
|--
  “ (valid_string str ) ”
  &&  “ (0 <= c_pre) ”
  &&  “ (c_pre <= 127) ”
  &&  “ ((string_length (str)) < INT_MAX) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (string_length (str))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < 0)) -> ((Znth (k) (str) (0)) <> c_pre)) ”
  &&  (store_string s_pre str )
) \/
(
forall (str: (@list Z)) (c_pre: Z) (PreH1 : (valid_string str )) (PreH2 : (0 <= c_pre)) (PreH3 : (c_pre <= 127)) (PreH4 : ((string_length (str)) < INT_MAX)),
  TT && emp 
|--
  “ forall (k: Z), (((0 <= k) /\ (k < 0)) -> ((Znth (k) (str) (0)) <> c_pre)) ”
  &&  “ (0 <= (string_length (str))) ”
  &&  emp
).

Definition strchr_entail_wit_1_split_goal_1 :=
forall (str: (@list Z)) (c_pre: Z) (PreH1 : (valid_string str )) (PreH2 : (0 <= c_pre)) (PreH3 : (c_pre <= 127)) (PreH4 : ((string_length (str)) < INT_MAX)),
  forall (k: Z), (((0 <= k) /\ (k < 0)) -> ((Znth (k) (str) (0)) <> c_pre))
.

Definition strchr_entail_wit_1_split_goal_2 :=
forall (str: (@list Z)) (c_pre: Z) (PreH1 : (valid_string str )) (PreH2 : (0 <= c_pre)) (PreH3 : (c_pre <= 127)) (PreH4 : ((string_length (str)) < INT_MAX)),
  (0 <= (string_length (str)))
.

Definition strchr_entail_wit_2 :=
(
forall (str: (@list Z)) (s_pre: Z) (c_pre: Z) (i: Z) (PreH1 : ((Znth i (c_string (str)) 0) <> c_pre)) (PreH2 : ((Znth i (c_string (str)) 0) <> 0)) (PreH3 : (valid_string str )) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : ((string_length (str)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre))),
  (store_string s_pre str )
|--
  “ (valid_string str ) ”
  &&  “ (0 <= c_pre) ”
  &&  “ (c_pre <= 127) ”
  &&  “ ((string_length (str)) < INT_MAX) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (string_length (str))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (str) (0)) <> c_pre)) ”
  &&  (store_string s_pre str )
) \/
(
forall (str: (@list Z)) (c_pre: Z) (i: Z) (PreH1 : ((Znth i (c_string (str)) 0) <> c_pre)) (PreH2 : ((Znth i (c_string (str)) 0) <> 0)) (PreH3 : (valid_string str )) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : ((string_length (str)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre))),
  TT && emp 
|--
  “ ((i + 1 ) <= (string_length (str))) ”
  &&  emp
).

Definition strchr_entail_wit_2_split_goal_1 :=
forall (str: (@list Z)) (c_pre: Z) (i: Z) (PreH1 : ((Znth i (c_string (str)) 0) <> c_pre)) (PreH2 : ((Znth i (c_string (str)) 0) <> 0)) (PreH3 : (valid_string str )) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : ((string_length (str)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre))),
  ((i + 1 ) <= (string_length (str)))
.

Definition strchr_return_wit_1 :=
(
forall (str: (@list Z)) (s_pre: Z) (c_pre: Z) (i: Z) (PreH1 : (c_pre <> 0)) (PreH2 : ((Znth i (c_string (str)) 0) = 0)) (PreH3 : (valid_string str )) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : ((string_length (str)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre))),
  (store_string s_pre str )
|--
  “ (strchr_result str c_pre 0 s_pre ) ”
  &&  (store_string s_pre str )
) \/
(
forall (str: (@list Z)) (s_pre: Z) (c_pre: Z) (i: Z) (PreH1 : (c_pre <> 0)) (PreH2 : ((Znth i (c_string (str)) 0) = 0)) (PreH3 : (valid_string str )) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : ((string_length (str)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre))),
  TT && emp 
|--
  “ (strchr_result str c_pre 0 s_pre ) ”
  &&  emp
).

Definition strchr_return_wit_1_split_goal_1 :=
forall (str: (@list Z)) (s_pre: Z) (c_pre: Z) (i: Z) (PreH1 : (c_pre <> 0)) (PreH2 : ((Znth i (c_string (str)) 0) = 0)) (PreH3 : (valid_string str )) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : ((string_length (str)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre))),
  (strchr_result str c_pre 0 s_pre )
.

Definition strchr_return_wit_2 :=
(
forall (str: (@list Z)) (s_pre: Z) (c_pre: Z) (i: Z) (PreH1 : (c_pre = 0)) (PreH2 : ((Znth i (c_string (str)) 0) = 0)) (PreH3 : (valid_string str )) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : ((string_length (str)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre))),
  (store_string s_pre str )
|--
  “ (strchr_result str c_pre (s_pre + (i * sizeof(CHAR))) s_pre ) ”
  &&  (store_string s_pre str )
) \/
(
forall (str: (@list Z)) (s_pre: Z) (c_pre: Z) (i: Z) (PreH1 : (c_pre = 0)) (PreH2 : ((Znth i (c_string (str)) 0) = 0)) (PreH3 : (valid_string str )) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : ((string_length (str)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre))),
  TT && emp 
|--
  “ (strchr_result str 0 (s_pre + (i * sizeof(CHAR))) s_pre ) ”
  &&  emp
).

Definition strchr_return_wit_2_split_goal_1 :=
forall (str: (@list Z)) (s_pre: Z) (c_pre: Z) (i: Z) (PreH1 : (c_pre = 0)) (PreH2 : ((Znth i (c_string (str)) 0) = 0)) (PreH3 : (valid_string str )) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : ((string_length (str)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre))),
  (strchr_result str 0 (s_pre + (i * sizeof(CHAR))) s_pre )
.

Definition strchr_return_wit_3 :=
(
forall (str: (@list Z)) (s_pre: Z) (c_pre: Z) (i: Z) (PreH1 : ((Znth i (c_string (str)) 0) = c_pre)) (PreH2 : ((Znth i (c_string (str)) 0) <> 0)) (PreH3 : (valid_string str )) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : ((string_length (str)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre))),
  (store_string s_pre str )
|--
  “ (strchr_result str c_pre (s_pre + (i * sizeof(CHAR))) s_pre ) ”
  &&  (store_string s_pre str )
) \/
(
forall (str: (@list Z)) (s_pre: Z) (c_pre: Z) (i: Z) (PreH1 : ((Znth i (c_string (str)) 0) = c_pre)) (PreH2 : ((Znth i (c_string (str)) 0) <> 0)) (PreH3 : (valid_string str )) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : ((string_length (str)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre))),
  TT && emp 
|--
  “ (strchr_result str c_pre (s_pre + (i * sizeof(CHAR))) s_pre ) ”
  &&  emp
).

Definition strchr_return_wit_3_split_goal_1 :=
forall (str: (@list Z)) (s_pre: Z) (c_pre: Z) (i: Z) (PreH1 : ((Znth i (c_string (str)) 0) = c_pre)) (PreH2 : ((Znth i (c_string (str)) 0) <> 0)) (PreH3 : (valid_string str )) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : ((string_length (str)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str)))) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < i)) -> ((Znth (k) (str) (0)) <> c_pre))),
  (strchr_result str c_pre (s_pre + (i * sizeof(CHAR))) s_pre )
.

Module Type VC_Correct.

Include string_Strategy_Correct.

Axiom proof_of_memchr_safety_wit_1 : memchr_safety_wit_1.
Axiom proof_of_memchr_safety_wit_2 : memchr_safety_wit_2.
Axiom proof_of_memchr_safety_wit_3 : memchr_safety_wit_3.
Axiom proof_of_memchr_entail_wit_1 : memchr_entail_wit_1.
Axiom proof_of_memchr_entail_wit_2 : memchr_entail_wit_2.
Axiom proof_of_memchr_return_wit_1 : memchr_return_wit_1.
Axiom proof_of_memchr_return_wit_2 : memchr_return_wit_2.
Axiom proof_of_memchr_partial_solve_wit_1 : memchr_partial_solve_wit_1.
Axiom proof_of_strchr_safety_wit_1 : strchr_safety_wit_1.
Axiom proof_of_strchr_safety_wit_2 : strchr_safety_wit_2.
Axiom proof_of_strchr_safety_wit_3 : strchr_safety_wit_3.
Axiom proof_of_strchr_safety_wit_4 : strchr_safety_wit_4.
Axiom proof_of_strchr_safety_wit_5 : strchr_safety_wit_5.
Axiom proof_of_strchr_entail_wit_1 : strchr_entail_wit_1.
Axiom proof_of_strchr_entail_wit_2 : strchr_entail_wit_2.
Axiom proof_of_strchr_return_wit_1 : strchr_return_wit_1.
Axiom proof_of_strchr_return_wit_2 : strchr_return_wit_2.
Axiom proof_of_strchr_return_wit_3 : strchr_return_wit_3.

End VC_Correct.
