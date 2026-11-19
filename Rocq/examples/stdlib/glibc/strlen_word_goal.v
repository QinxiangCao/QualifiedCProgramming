From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.stdlib.glibc.strlen_word_lib.
Import StrlenLittleEndian strlen_word_lib.
Local Open Scope sac.

(*----- Function sl_load_word -----*)

Definition sl_load_word_entail_wit_1 :=
(
forall (bytes: (@list Z)) (capacity: Z) (s: Z) (p_pre: Z) (PreH1 : (0 <= s)) (PreH2 : (s <= (sl_addr (p_pre)))) (PreH3 : (((sl_addr (p_pre)) + 8 ) <= (s + capacity ))) (PreH4 : ((s + capacity ) <= UINT64_MAX)) (PreH5 : (((sl_addr (p_pre)) % ( 8 ) ) = 0)),
  (UCharArray.full s capacity bytes )
|--
  EX (word: Z),
  “ ((Zlength (bytes)) = capacity) ”
  &&  “ (0 <= s) ”
  &&  “ (s <= (sl_addr (p_pre))) ”
  &&  “ (((sl_addr (p_pre)) + 8 ) <= (s + capacity )) ”
  &&  “ ((s + capacity ) <= UINT64_MAX) ”
  &&  “ (((sl_addr (p_pre)) % ( 8 ) ) = 0) ”
  &&  “ (0 <= word) ”
  &&  “ (word <= UINT64_MAX) ”
  &&  “ (sl_word_matches word bytes ((sl_addr (p_pre)) - s ) ) ”
  &&  ((p_pre) # UInt64  |-> word)
  **  (UCharArray.seg s 0 ((sl_addr (p_pre)) - s ) (sublist (0) (((sl_addr (p_pre)) - s )) (bytes)) )
  **  (UCharArray.seg s (((sl_addr (p_pre)) - s ) + 8 ) capacity (sublist ((((sl_addr (p_pre)) - s ) + 8 )) (capacity) (bytes)) )
) \/
(
forall (bytes: (@list Z)) (capacity: Z) (s: Z) (p_pre: Z) (PreH1 : (0 <= s)) (PreH2 : (s <= (sl_addr (p_pre)))) (PreH3 : (((sl_addr (p_pre)) + 8 ) <= (s + capacity ))) (PreH4 : ((s + capacity ) <= UINT64_MAX)) (PreH5 : (((sl_addr (p_pre)) % ( 8 ) ) = 0)),
  (UCharArray.full s capacity bytes )
|--
  EX (word: Z),
  “ ((Zlength (bytes)) = capacity) ”
  &&  “ (0 <= s) ”
  &&  “ (s <= (sl_addr (p_pre))) ”
  &&  “ (((sl_addr (p_pre)) + 8 ) <= (s + capacity )) ”
  &&  “ ((s + capacity ) <= UINT64_MAX) ”
  &&  “ (((sl_addr (p_pre)) % ( 8 ) ) = 0) ”
  &&  “ (0 <= word) ”
  &&  “ (word <= UINT64_MAX) ”
  &&  “ (sl_word_matches word bytes ((sl_addr (p_pre)) - s ) ) ”
  &&  ((p_pre) # UInt64  |-> word)
  **  (UCharArray.seg s 0 ((sl_addr (p_pre)) - s ) (sublist (0) (((sl_addr (p_pre)) - s )) (bytes)) )
  **  (UCharArray.seg s (((sl_addr (p_pre)) - s ) + 8 ) capacity (sublist ((((sl_addr (p_pre)) - s ) + 8 )) (capacity) (bytes)) )
).

Definition sl_load_word_return_wit_1 :=
(
forall (bytes: (@list Z)) (capacity: Z) (s: Z) (p_pre: Z) (word: Z) (PreH1 : ((Zlength (bytes)) = capacity)) (PreH2 : (0 <= s)) (PreH3 : (s <= (sl_addr (p_pre)))) (PreH4 : (((sl_addr (p_pre)) + 8 ) <= (s + capacity ))) (PreH5 : ((s + capacity ) <= UINT64_MAX)) (PreH6 : (((sl_addr (p_pre)) % ( 8 ) ) = 0)) (PreH7 : (0 <= word)) (PreH8 : (word <= UINT64_MAX)) (PreH9 : (sl_word_matches word bytes ((sl_addr (p_pre)) - s ) )),
  ((p_pre) # UInt64  |-> word)
  **  (UCharArray.seg s 0 ((sl_addr (p_pre)) - s ) (sublist (0) (((sl_addr (p_pre)) - s )) (bytes)) )
  **  (UCharArray.seg s (((sl_addr (p_pre)) - s ) + 8 ) capacity (sublist ((((sl_addr (p_pre)) - s ) + 8 )) (capacity) (bytes)) )
|--
  “ (sl_word_matches word bytes ((sl_addr (p_pre)) - s ) ) ”
  &&  “ (0 <= word) ”
  &&  “ (word <= UINT64_MAX) ”
  &&  (UCharArray.full s capacity bytes )
) \/
(
forall (bytes: (@list Z)) (capacity: Z) (s: Z) (p_pre: Z) (word: Z) (PreH1 : (word <= UINT64_MAX)) (PreH2 : (word >= 0)) (PreH3 : ((Zlength (bytes)) = capacity)) (PreH4 : (0 <= s)) (PreH5 : (s <= (sl_addr (p_pre)))) (PreH6 : (((sl_addr (p_pre)) + 8 ) <= (s + capacity ))) (PreH7 : ((s + capacity ) <= UINT64_MAX)) (PreH8 : (((sl_addr (p_pre)) % ( 8 ) ) = 0)) (PreH9 : (0 <= word)) (PreH10 : (word <= UINT64_MAX)) (PreH11 : (sl_word_matches word bytes ((sl_addr (p_pre)) - s ) )),
  ((p_pre) # UInt64  |-> word)
  **  (UCharArray.seg s 0 ((sl_addr (p_pre)) - s ) (sublist (0) (((sl_addr (p_pre)) - s )) (bytes)) )
  **  (UCharArray.seg s (((sl_addr (p_pre)) - s ) + 8 ) capacity (sublist ((((sl_addr (p_pre)) - s ) + 8 )) (capacity) (bytes)) )
|--
  (UCharArray.full s capacity bytes )
).

Definition sl_load_word_return_wit_1_split_goal_spatial :=
forall (bytes: (@list Z)) (capacity: Z) (s: Z) (p_pre: Z) (word: Z) (PreH1 : (word <= UINT64_MAX)) (PreH2 : (word >= 0)) (PreH3 : ((Zlength (bytes)) = capacity)) (PreH4 : (0 <= s)) (PreH5 : (s <= (sl_addr (p_pre)))) (PreH6 : (((sl_addr (p_pre)) + 8 ) <= (s + capacity ))) (PreH7 : ((s + capacity ) <= UINT64_MAX)) (PreH8 : (((sl_addr (p_pre)) % ( 8 ) ) = 0)) (PreH9 : (0 <= word)) (PreH10 : (word <= UINT64_MAX)) (PreH11 : (sl_word_matches word bytes ((sl_addr (p_pre)) - s ) )),
  ((p_pre) # UInt64  |-> word)
  **  (UCharArray.seg s 0 ((sl_addr (p_pre)) - s ) (sublist (0) (((sl_addr (p_pre)) - s )) (bytes)) )
  **  (UCharArray.seg s (((sl_addr (p_pre)) - s ) + 8 ) capacity (sublist ((((sl_addr (p_pre)) - s ) + 8 )) (capacity) (bytes)) )
|--
  (UCharArray.full s capacity bytes )
.

(*----- Function sl_first_zero -----*)

Definition sl_first_zero_safety_wit_1 :=
forall (w_pre: Z) (start_pre: Z) (PreH1 : (0 <= start_pre)) (PreH2 : (start_pre < 8)) (PreH3 : (0 <= w_pre)) (PreH4 : (w_pre <= UINT64_MAX)),
  ((( &( "i" ) )) # UInt64  |->_)
  **  ((( &( "w" ) )) # UInt64  |-> w_pre)
  **  ((( &( "start" ) )) # UInt64  |-> start_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sl_first_zero_safety_wit_2 :=
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : (i < start_pre)) (PreH2 : (0 <= start_pre)) (PreH3 : (start_pre < 8)) (PreH4 : (0 <= i)) (PreH5 : (i <= start_pre)) (PreH6 : (0 <= w_pre)) (PreH7 : (w_pre <= UINT64_MAX)) (PreH8 : (0 <= v)) (PreH9 : (v <= UINT64_MAX)) (PreH10 : (v = (sl_suffix (w_pre) (i)))),
  ((( &( "w" ) )) # UInt64  |-> w_pre)
  **  ((( &( "start" ) )) # UInt64  |-> start_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "v" ) )) # UInt64  |-> v)
|--
  “ (256 <> 0) ”
.

Definition sl_first_zero_safety_wit_3 :=
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : (i < start_pre)) (PreH2 : (0 <= start_pre)) (PreH3 : (start_pre < 8)) (PreH4 : (0 <= i)) (PreH5 : (i <= start_pre)) (PreH6 : (0 <= w_pre)) (PreH7 : (w_pre <= UINT64_MAX)) (PreH8 : (0 <= v)) (PreH9 : (v <= UINT64_MAX)) (PreH10 : (v = (sl_suffix (w_pre) (i)))),
  ((( &( "w" ) )) # UInt64  |-> w_pre)
  **  ((( &( "start" ) )) # UInt64  |-> start_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "v" ) )) # UInt64  |-> v)
|--
  “ (256 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 256) ”
.

Definition sl_first_zero_safety_wit_4 :=
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : (0 <= start_pre)) (PreH2 : (start_pre < 8)) (PreH3 : (start_pre <= i)) (PreH4 : (i <= 8)) (PreH5 : (0 <= w_pre)) (PreH6 : (w_pre <= UINT64_MAX)) (PreH7 : (0 <= v)) (PreH8 : (v <= UINT64_MAX)) (PreH9 : (v = (sl_suffix (w_pre) (i)))) (PreH10 : forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0))),
  ((( &( "w" ) )) # UInt64  |-> w_pre)
  **  ((( &( "start" ) )) # UInt64  |-> start_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "v" ) )) # UInt64  |-> v)
|--
  “ (8 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 8) ”
.

Definition sl_first_zero_safety_wit_5 :=
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= start_pre)) (PreH3 : (start_pre < 8)) (PreH4 : (start_pre <= i)) (PreH5 : (i <= 8)) (PreH6 : (0 <= w_pre)) (PreH7 : (w_pre <= UINT64_MAX)) (PreH8 : (0 <= v)) (PreH9 : (v <= UINT64_MAX)) (PreH10 : (v = (sl_suffix (w_pre) (i)))) (PreH11 : forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0))),
  ((( &( "w" ) )) # UInt64  |-> w_pre)
  **  ((( &( "start" ) )) # UInt64  |-> start_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "v" ) )) # UInt64  |-> v)
|--
  “ (256 <> 0) ”
.

Definition sl_first_zero_safety_wit_6 :=
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= start_pre)) (PreH3 : (start_pre < 8)) (PreH4 : (start_pre <= i)) (PreH5 : (i <= 8)) (PreH6 : (0 <= w_pre)) (PreH7 : (w_pre <= UINT64_MAX)) (PreH8 : (0 <= v)) (PreH9 : (v <= UINT64_MAX)) (PreH10 : (v = (sl_suffix (w_pre) (i)))) (PreH11 : forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0))),
  ((( &( "w" ) )) # UInt64  |-> w_pre)
  **  ((( &( "start" ) )) # UInt64  |-> start_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "v" ) )) # UInt64  |-> v)
|--
  “ (256 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 256) ”
.

Definition sl_first_zero_safety_wit_7 :=
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= start_pre)) (PreH3 : (start_pre < 8)) (PreH4 : (start_pre <= i)) (PreH5 : (i <= 8)) (PreH6 : (0 <= w_pre)) (PreH7 : (w_pre <= UINT64_MAX)) (PreH8 : (0 <= v)) (PreH9 : (v <= UINT64_MAX)) (PreH10 : (v = (sl_suffix (w_pre) (i)))) (PreH11 : forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0))),
  ((( &( "w" ) )) # UInt64  |-> w_pre)
  **  ((( &( "start" ) )) # UInt64  |-> start_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "v" ) )) # UInt64  |-> v)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sl_first_zero_safety_wit_8 :=
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : ((v % ( 256 ) ) <> 0)) (PreH2 : (i < 8)) (PreH3 : (0 <= start_pre)) (PreH4 : (start_pre < 8)) (PreH5 : (start_pre <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= w_pre)) (PreH8 : (w_pre <= UINT64_MAX)) (PreH9 : (0 <= v)) (PreH10 : (v <= UINT64_MAX)) (PreH11 : (v = (sl_suffix (w_pre) (i)))) (PreH12 : forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0))),
  ((( &( "w" ) )) # UInt64  |-> w_pre)
  **  ((( &( "start" ) )) # UInt64  |-> start_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "v" ) )) # UInt64  |-> v)
|--
  “ (256 <> 0) ”
.

Definition sl_first_zero_safety_wit_9 :=
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : ((v % ( 256 ) ) <> 0)) (PreH2 : (i < 8)) (PreH3 : (0 <= start_pre)) (PreH4 : (start_pre < 8)) (PreH5 : (start_pre <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= w_pre)) (PreH8 : (w_pre <= UINT64_MAX)) (PreH9 : (0 <= v)) (PreH10 : (v <= UINT64_MAX)) (PreH11 : (v = (sl_suffix (w_pre) (i)))) (PreH12 : forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0))),
  ((( &( "w" ) )) # UInt64  |-> w_pre)
  **  ((( &( "start" ) )) # UInt64  |-> start_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "v" ) )) # UInt64  |-> v)
|--
  “ (256 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 256) ”
.

Definition sl_first_zero_safety_wit_10 :=
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= start_pre)) (PreH3 : (start_pre < 8)) (PreH4 : (start_pre <= i)) (PreH5 : (i <= 8)) (PreH6 : (0 <= w_pre)) (PreH7 : (w_pre <= UINT64_MAX)) (PreH8 : (0 <= v)) (PreH9 : (v <= UINT64_MAX)) (PreH10 : (v = (sl_suffix (w_pre) (i)))) (PreH11 : forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0))),
  ((( &( "w" ) )) # UInt64  |-> w_pre)
  **  ((( &( "start" ) )) # UInt64  |-> start_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "v" ) )) # UInt64  |-> v)
|--
  “ (8 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 8) ”
.

Definition sl_first_zero_entail_wit_1 :=
(
forall (w_pre: Z) (start_pre: Z) (PreH1 : (0 <= start_pre)) (PreH2 : (start_pre < 8)) (PreH3 : (0 <= w_pre)) (PreH4 : (w_pre <= UINT64_MAX)),
  TT && emp 
|--
  “ (0 <= start_pre) ”
  &&  “ (start_pre < 8) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= start_pre) ”
  &&  “ (0 <= w_pre) ”
  &&  “ (w_pre <= UINT64_MAX) ”
  &&  “ (0 <= w_pre) ”
  &&  “ (w_pre <= UINT64_MAX) ”
  &&  “ (w_pre = (sl_suffix (w_pre) (0))) ”
  &&  emp
) \/
(
forall (w_pre: Z) (start_pre: Z) (PreH1 : (0 <= start_pre)) (PreH2 : (start_pre < 8)) (PreH3 : (0 <= w_pre)) (PreH4 : (w_pre <= UINT64_MAX)),
  TT && emp 
|--
  “ (w_pre = (sl_suffix (w_pre) (0))) ”
  &&  emp
).

Definition sl_first_zero_entail_wit_1_split_goal_1 :=
forall (w_pre: Z) (start_pre: Z) (PreH1 : (0 <= start_pre)) (PreH2 : (start_pre < 8)) (PreH3 : (0 <= w_pre)) (PreH4 : (w_pre <= UINT64_MAX)),
  (w_pre = (sl_suffix (w_pre) (0)))
.

Definition sl_first_zero_entail_wit_2 :=
(
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : (i < start_pre)) (PreH2 : (0 <= start_pre)) (PreH3 : (start_pre < 8)) (PreH4 : (0 <= i)) (PreH5 : (i <= start_pre)) (PreH6 : (0 <= w_pre)) (PreH7 : (w_pre <= UINT64_MAX)) (PreH8 : (0 <= v)) (PreH9 : (v <= UINT64_MAX)) (PreH10 : (v = (sl_suffix (w_pre) (i)))),
  TT && emp 
|--
  “ (0 <= start_pre) ”
  &&  “ (start_pre < 8) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= start_pre) ”
  &&  “ (0 <= w_pre) ”
  &&  “ (w_pre <= UINT64_MAX) ”
  &&  “ (0 <= (v ÷ 256 )) ”
  &&  “ ((v ÷ 256 ) <= UINT64_MAX) ”
  &&  “ ((v ÷ 256 ) = (sl_suffix (w_pre) ((i + 1 )))) ”
  &&  emp
) \/
(
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : (i < start_pre)) (PreH2 : (0 <= start_pre)) (PreH3 : (start_pre < 8)) (PreH4 : (0 <= i)) (PreH5 : (i <= start_pre)) (PreH6 : (0 <= w_pre)) (PreH7 : (w_pre <= UINT64_MAX)) (PreH8 : (0 <= v)) (PreH9 : (v <= UINT64_MAX)) (PreH10 : (v = (sl_suffix (w_pre) (i)))),
  TT && emp 
|--
  “ ((v ÷ 256 ) = (sl_suffix (w_pre) ((i + 1 )))) ”
  &&  “ ((v ÷ 256 ) <= UINT64_MAX) ”
  &&  “ (0 <= (v ÷ 256 )) ”
  &&  emp
).

Definition sl_first_zero_entail_wit_2_split_goal_1 :=
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : (i < start_pre)) (PreH2 : (0 <= start_pre)) (PreH3 : (start_pre < 8)) (PreH4 : (0 <= i)) (PreH5 : (i <= start_pre)) (PreH6 : (0 <= w_pre)) (PreH7 : (w_pre <= UINT64_MAX)) (PreH8 : (0 <= v)) (PreH9 : (v <= UINT64_MAX)) (PreH10 : (v = (sl_suffix (w_pre) (i)))),
  ((v ÷ 256 ) = (sl_suffix (w_pre) ((i + 1 ))))
.

Definition sl_first_zero_entail_wit_2_split_goal_2 :=
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : (i < start_pre)) (PreH2 : (0 <= start_pre)) (PreH3 : (start_pre < 8)) (PreH4 : (0 <= i)) (PreH5 : (i <= start_pre)) (PreH6 : (0 <= w_pre)) (PreH7 : (w_pre <= UINT64_MAX)) (PreH8 : (0 <= v)) (PreH9 : (v <= UINT64_MAX)) (PreH10 : (v = (sl_suffix (w_pre) (i)))),
  ((v ÷ 256 ) <= UINT64_MAX)
.

Definition sl_first_zero_entail_wit_2_split_goal_3 :=
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : (i < start_pre)) (PreH2 : (0 <= start_pre)) (PreH3 : (start_pre < 8)) (PreH4 : (0 <= i)) (PreH5 : (i <= start_pre)) (PreH6 : (0 <= w_pre)) (PreH7 : (w_pre <= UINT64_MAX)) (PreH8 : (0 <= v)) (PreH9 : (v <= UINT64_MAX)) (PreH10 : (v = (sl_suffix (w_pre) (i)))),
  (0 <= (v ÷ 256 ))
.

Definition sl_first_zero_entail_wit_3 :=
(
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : (i >= start_pre)) (PreH2 : (0 <= start_pre)) (PreH3 : (start_pre < 8)) (PreH4 : (0 <= i)) (PreH5 : (i <= start_pre)) (PreH6 : (0 <= w_pre)) (PreH7 : (w_pre <= UINT64_MAX)) (PreH8 : (0 <= v)) (PreH9 : (v <= UINT64_MAX)) (PreH10 : (v = (sl_suffix (w_pre) (i)))),
  TT && emp 
|--
  “ (0 <= start_pre) ”
  &&  “ (start_pre < 8) ”
  &&  “ (start_pre <= i) ”
  &&  “ (i <= 8) ”
  &&  “ (0 <= w_pre) ”
  &&  “ (w_pre <= UINT64_MAX) ”
  &&  “ (0 <= v) ”
  &&  “ (v <= UINT64_MAX) ”
  &&  “ (v = (sl_suffix (w_pre) (i))) ”
  &&  “ forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0)) ”
  &&  emp
) \/
(
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : (i >= start_pre)) (PreH2 : (0 <= start_pre)) (PreH3 : (start_pre < 8)) (PreH4 : (0 <= i)) (PreH5 : (i <= start_pre)) (PreH6 : (0 <= w_pre)) (PreH7 : (w_pre <= UINT64_MAX)) (PreH8 : (0 <= v)) (PreH9 : (v <= UINT64_MAX)) (PreH10 : (v = (sl_suffix (w_pre) (i)))),
  TT && emp 
|--
  “ forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0)) ”
  &&  emp
).

Definition sl_first_zero_entail_wit_3_split_goal_1 :=
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : (i >= start_pre)) (PreH2 : (0 <= start_pre)) (PreH3 : (start_pre < 8)) (PreH4 : (0 <= i)) (PreH5 : (i <= start_pre)) (PreH6 : (0 <= w_pre)) (PreH7 : (w_pre <= UINT64_MAX)) (PreH8 : (0 <= v)) (PreH9 : (v <= UINT64_MAX)) (PreH10 : (v = (sl_suffix (w_pre) (i)))),
  forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0))
.

Definition sl_first_zero_entail_wit_4 :=
(
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : ((v % ( 256 ) ) <> 0)) (PreH2 : (i < 8)) (PreH3 : (0 <= start_pre)) (PreH4 : (start_pre < 8)) (PreH5 : (start_pre <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= w_pre)) (PreH8 : (w_pre <= UINT64_MAX)) (PreH9 : (0 <= v)) (PreH10 : (v <= UINT64_MAX)) (PreH11 : (v = (sl_suffix (w_pre) (i)))) (PreH12 : forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0))),
  TT && emp 
|--
  “ (0 <= start_pre) ”
  &&  “ (start_pre < 8) ”
  &&  “ (start_pre <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= 8) ”
  &&  “ (0 <= w_pre) ”
  &&  “ (w_pre <= UINT64_MAX) ”
  &&  “ (0 <= (v ÷ 256 )) ”
  &&  “ ((v ÷ 256 ) <= UINT64_MAX) ”
  &&  “ ((v ÷ 256 ) = (sl_suffix (w_pre) ((i + 1 )))) ”
  &&  “ forall (j: Z), (((start_pre <= j) /\ (j < (i + 1 ))) -> ((sl_byte (w_pre) (j)) <> 0)) ”
  &&  emp
) \/
(
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : ((v % ( 256 ) ) <> 0)) (PreH2 : (i < 8)) (PreH3 : (0 <= start_pre)) (PreH4 : (start_pre < 8)) (PreH5 : (start_pre <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= w_pre)) (PreH8 : (w_pre <= UINT64_MAX)) (PreH9 : (0 <= v)) (PreH10 : (v <= UINT64_MAX)) (PreH11 : (v = (sl_suffix (w_pre) (i)))) (PreH12 : forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0))),
  TT && emp 
|--
  “ ((v ÷ 256 ) = (sl_suffix (w_pre) ((i + 1 )))) ”
  &&  “ ((v ÷ 256 ) <= UINT64_MAX) ”
  &&  “ (0 <= (v ÷ 256 )) ”
  &&  emp
).

Definition sl_first_zero_entail_wit_4_split_goal_1 :=
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : ((v % ( 256 ) ) <> 0)) (PreH2 : (i < 8)) (PreH3 : (0 <= start_pre)) (PreH4 : (start_pre < 8)) (PreH5 : (start_pre <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= w_pre)) (PreH8 : (w_pre <= UINT64_MAX)) (PreH9 : (0 <= v)) (PreH10 : (v <= UINT64_MAX)) (PreH11 : (v = (sl_suffix (w_pre) (i)))) (PreH12 : forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0))),
  ((v ÷ 256 ) = (sl_suffix (w_pre) ((i + 1 ))))
.

Definition sl_first_zero_entail_wit_4_split_goal_2 :=
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : ((v % ( 256 ) ) <> 0)) (PreH2 : (i < 8)) (PreH3 : (0 <= start_pre)) (PreH4 : (start_pre < 8)) (PreH5 : (start_pre <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= w_pre)) (PreH8 : (w_pre <= UINT64_MAX)) (PreH9 : (0 <= v)) (PreH10 : (v <= UINT64_MAX)) (PreH11 : (v = (sl_suffix (w_pre) (i)))) (PreH12 : forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0))),
  ((v ÷ 256 ) <= UINT64_MAX)
.

Definition sl_first_zero_entail_wit_4_split_goal_3 :=
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : ((v % ( 256 ) ) <> 0)) (PreH2 : (i < 8)) (PreH3 : (0 <= start_pre)) (PreH4 : (start_pre < 8)) (PreH5 : (start_pre <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= w_pre)) (PreH8 : (w_pre <= UINT64_MAX)) (PreH9 : (0 <= v)) (PreH10 : (v <= UINT64_MAX)) (PreH11 : (v = (sl_suffix (w_pre) (i)))) (PreH12 : forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0))),
  (0 <= (v ÷ 256 ))
.

Definition sl_first_zero_return_wit_1 :=
(
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= start_pre)) (PreH3 : (start_pre < 8)) (PreH4 : (start_pre <= i)) (PreH5 : (i <= 8)) (PreH6 : (0 <= w_pre)) (PreH7 : (w_pre <= UINT64_MAX)) (PreH8 : (0 <= v)) (PreH9 : (v <= UINT64_MAX)) (PreH10 : (v = (sl_suffix (w_pre) (i)))) (PreH11 : forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0))),
  TT && emp 
|--
  “ (sl_found w_pre start_pre 8 ) ”
  &&  emp
) \/
(
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= start_pre)) (PreH3 : (start_pre < 8)) (PreH4 : (start_pre <= i)) (PreH5 : (i <= 8)) (PreH6 : (0 <= w_pre)) (PreH7 : (w_pre <= UINT64_MAX)) (PreH8 : (0 <= v)) (PreH9 : (v <= UINT64_MAX)) (PreH10 : (v = (sl_suffix (w_pre) (i)))) (PreH11 : forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0))),
  TT && emp 
|--
  “ (sl_found w_pre start_pre 8 ) ”
  &&  emp
).

Definition sl_first_zero_return_wit_1_split_goal_1 :=
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= start_pre)) (PreH3 : (start_pre < 8)) (PreH4 : (start_pre <= i)) (PreH5 : (i <= 8)) (PreH6 : (0 <= w_pre)) (PreH7 : (w_pre <= UINT64_MAX)) (PreH8 : (0 <= v)) (PreH9 : (v <= UINT64_MAX)) (PreH10 : (v = (sl_suffix (w_pre) (i)))) (PreH11 : forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0))),
  (sl_found w_pre start_pre 8 )
.

Definition sl_first_zero_return_wit_2 :=
(
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : ((v % ( 256 ) ) = 0)) (PreH2 : (i < 8)) (PreH3 : (0 <= start_pre)) (PreH4 : (start_pre < 8)) (PreH5 : (start_pre <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= w_pre)) (PreH8 : (w_pre <= UINT64_MAX)) (PreH9 : (0 <= v)) (PreH10 : (v <= UINT64_MAX)) (PreH11 : (v = (sl_suffix (w_pre) (i)))) (PreH12 : forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0))),
  TT && emp 
|--
  “ (sl_found w_pre start_pre i ) ”
  &&  emp
) \/
(
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : ((v % ( 256 ) ) = 0)) (PreH2 : (i < 8)) (PreH3 : (0 <= start_pre)) (PreH4 : (start_pre < 8)) (PreH5 : (start_pre <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= w_pre)) (PreH8 : (w_pre <= UINT64_MAX)) (PreH9 : (0 <= v)) (PreH10 : (v <= UINT64_MAX)) (PreH11 : (v = (sl_suffix (w_pre) (i)))) (PreH12 : forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0))),
  TT && emp 
|--
  “ (sl_found w_pre start_pre i ) ”
  &&  emp
).

Definition sl_first_zero_return_wit_2_split_goal_1 :=
forall (w_pre: Z) (start_pre: Z) (v: Z) (i: Z) (PreH1 : ((v % ( 256 ) ) = 0)) (PreH2 : (i < 8)) (PreH3 : (0 <= start_pre)) (PreH4 : (start_pre < 8)) (PreH5 : (start_pre <= i)) (PreH6 : (i <= 8)) (PreH7 : (0 <= w_pre)) (PreH8 : (w_pre <= UINT64_MAX)) (PreH9 : (0 <= v)) (PreH10 : (v <= UINT64_MAX)) (PreH11 : (v = (sl_suffix (w_pre) (i)))) (PreH12 : forall (j: Z), (((start_pre <= j) /\ (j < i)) -> ((sl_byte (w_pre) (j)) <> 0))),
  (sl_found w_pre start_pre i )
.

(*----- Function strlen_word -----*)

Definition strlen_word_safety_wit_1 :=
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (PreH1 : (0 <= s_pre)) (PreH2 : ((s_pre % ( 8 ) ) = 0)) (PreH3 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH4 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)),
  ((( &( "start" ) )) # UInt64  |->_)
  **  ((( &( "address" ) )) # UInt64  |-> (unsigned_last_nbits (s_pre) (64)))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (ObjectString.store_string s_pre capacity_capacity_spec m_capacity_spec )
|--
  “ (8 <> 0) ”
.

Definition strlen_word_safety_wit_2 :=
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (PreH1 : (0 <= s_pre)) (PreH2 : ((s_pre % ( 8 ) ) = 0)) (PreH3 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH4 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)),
  ((( &( "start" ) )) # UInt64  |->_)
  **  ((( &( "address" ) )) # UInt64  |-> (unsigned_last_nbits (s_pre) (64)))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (ObjectString.store_string s_pre capacity_capacity_spec m_capacity_spec )
|--
  “ (8 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 8) ”
.

Definition strlen_word_safety_wit_3 :=
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (tail: (@list Z)) (p: Z) (start: Z) (address: Z) (PreH1 : (address = s_pre)) (PreH2 : (start = 0)) (PreH3 : (0 <= s_pre)) (PreH4 : ((s_pre % ( 8 ) ) = 0)) (PreH5 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH6 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)) (PreH7 : (s_pre <= p)) (PreH8 : (p <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR))))) (PreH9 : ((p % ( 8 ) ) = 0)) (PreH10 : (StrlenLittleEndian.valid_string m_capacity_spec )),
  ((( &( "address" ) )) # UInt64  |-> address)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "start" ) )) # UInt64  |-> start)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition strlen_word_safety_wit_4 :=
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (tail: (@list Z)) (p: Z) (start: Z) (address: Z) (retval: Z) (retval_2: Z) (PreH1 : (sl_found retval start retval_2 )) (PreH2 : (sl_word_matches retval (app (m_capacity_spec) ((cons (0) (tail)))) ((sl_addr (p)) - s_pre ) )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= UINT64_MAX)) (PreH5 : (address = s_pre)) (PreH6 : (start = 0)) (PreH7 : (0 <= s_pre)) (PreH8 : ((s_pre % ( 8 ) ) = 0)) (PreH9 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH10 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)) (PreH11 : (s_pre <= p)) (PreH12 : (p <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR))))) (PreH13 : ((p % ( 8 ) ) = 0)) (PreH14 : (StrlenLittleEndian.valid_string m_capacity_spec )),
  ((( &( "k" ) )) # UInt64  |-> retval_2)
  **  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
  **  ((( &( "w" ) )) # UInt64  |-> retval)
  **  ((( &( "address" ) )) # UInt64  |-> address)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "start" ) )) # UInt64  |-> start)
  **  ((( &( "p" ) )) # UInt64  |-> p)
|--
  “ (8 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 8) ”
.

Definition strlen_word_safety_wit_5 :=
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (tail: (@list Z)) (p: Z) (start: Z) (address: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 >= 8)) (PreH2 : (sl_found retval start retval_2 )) (PreH3 : (sl_word_matches retval (app (m_capacity_spec) ((cons (0) (tail)))) ((sl_addr (p)) - s_pre ) )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= UINT64_MAX)) (PreH6 : (address = s_pre)) (PreH7 : (start = 0)) (PreH8 : (0 <= s_pre)) (PreH9 : ((s_pre % ( 8 ) ) = 0)) (PreH10 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)) (PreH12 : (s_pre <= p)) (PreH13 : (p <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR))))) (PreH14 : ((p % ( 8 ) ) = 0)) (PreH15 : (StrlenLittleEndian.valid_string m_capacity_spec )),
  ((( &( "k" ) )) # UInt64  |-> retval_2)
  **  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
  **  ((( &( "w" ) )) # UInt64  |-> retval)
  **  ((( &( "address" ) )) # UInt64  |-> address)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "start" ) )) # UInt64  |-> start)
  **  ((( &( "p" ) )) # UInt64  |-> p)
|--
  “ (8 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 8) ”
.

Definition strlen_word_safety_wit_6 :=
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (tail: (@list Z)) (p: Z) (start: Z) (address: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 >= 8)) (PreH2 : (sl_found retval start retval_2 )) (PreH3 : (sl_word_matches retval (app (m_capacity_spec) ((cons (0) (tail)))) ((sl_addr (p)) - s_pre ) )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= UINT64_MAX)) (PreH6 : (address = s_pre)) (PreH7 : (start = 0)) (PreH8 : (0 <= s_pre)) (PreH9 : ((s_pre % ( 8 ) ) = 0)) (PreH10 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)) (PreH12 : (s_pre <= p)) (PreH13 : (p <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR))))) (PreH14 : ((p % ( 8 ) ) = 0)) (PreH15 : (StrlenLittleEndian.valid_string m_capacity_spec )),
  ((( &( "k" ) )) # UInt64  |-> retval_2)
  **  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
  **  ((( &( "w" ) )) # UInt64  |-> retval)
  **  ((( &( "address" ) )) # UInt64  |-> address)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "start" ) )) # UInt64  |-> start)
  **  ((( &( "p" ) )) # UInt64  |-> (unsigned_last_nbits ((p + 8 )) (64)))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strlen_word_entail_wit_1 :=
(
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (PreH1 : (0 <= s_pre)) (PreH2 : ((s_pre % ( 8 ) ) = 0)) (PreH3 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH4 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)),
  (ObjectString.store_string s_pre capacity_capacity_spec m_capacity_spec )
|--
  EX (tail: (@list Z)),
  “ ((unsigned_last_nbits (s_pre) (64)) = s_pre) ”
  &&  “ (((unsigned_last_nbits (s_pre) (64)) % ( 8 ) ) = 0) ”
  &&  “ (0 <= s_pre) ”
  &&  “ ((s_pre % ( 8 ) ) = 0) ”
  &&  “ ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec) ”
  &&  “ (s_pre <= (unsigned_last_nbits (((unsigned_last_nbits (s_pre) (64)) - ((unsigned_last_nbits (s_pre) (64)) % ( 8 ) ) )) (64))) ”
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (s_pre) (64)) - ((unsigned_last_nbits (s_pre) (64)) % ( 8 ) ) )) (64)) <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR)))) ”
  &&  “ (((unsigned_last_nbits (((unsigned_last_nbits (s_pre) (64)) - ((unsigned_last_nbits (s_pre) (64)) % ( 8 ) ) )) (64)) % ( 8 ) ) = 0) ”
  &&  “ (StrlenLittleEndian.valid_string m_capacity_spec ) ”
  &&  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
) \/
(
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (PreH1 : (0 <= s_pre)) (PreH2 : ((s_pre % ( 8 ) ) = 0)) (PreH3 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH4 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)),
  (ObjectString.store_string s_pre capacity_capacity_spec m_capacity_spec )
|--
  EX (tail: (@list Z)),
  “ ((unsigned_last_nbits (s_pre) (64)) = s_pre) ”
  &&  “ (((unsigned_last_nbits (s_pre) (64)) % ( 8 ) ) = 0) ”
  &&  “ (0 <= s_pre) ”
  &&  “ ((s_pre % ( 8 ) ) = 0) ”
  &&  “ ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec) ”
  &&  “ (s_pre <= (unsigned_last_nbits (((unsigned_last_nbits (s_pre) (64)) - ((unsigned_last_nbits (s_pre) (64)) % ( 8 ) ) )) (64))) ”
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (s_pre) (64)) - ((unsigned_last_nbits (s_pre) (64)) % ( 8 ) ) )) (64)) <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR)))) ”
  &&  “ (((unsigned_last_nbits (((unsigned_last_nbits (s_pre) (64)) - ((unsigned_last_nbits (s_pre) (64)) % ( 8 ) ) )) (64)) % ( 8 ) ) = 0) ”
  &&  “ (StrlenLittleEndian.valid_string m_capacity_spec ) ”
  &&  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
).

Definition strlen_word_entail_wit_2 :=
(
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (tail_2: (@list Z)) (p: Z) (start: Z) (address: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 >= 8)) (PreH2 : (sl_found retval start retval_2 )) (PreH3 : (sl_word_matches retval (app (m_capacity_spec) ((cons (0) (tail_2)))) ((sl_addr (p)) - s_pre ) )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= UINT64_MAX)) (PreH6 : (address = s_pre)) (PreH7 : (start = 0)) (PreH8 : (0 <= s_pre)) (PreH9 : ((s_pre % ( 8 ) ) = 0)) (PreH10 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)) (PreH12 : (s_pre <= p)) (PreH13 : (p <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR))))) (PreH14 : ((p % ( 8 ) ) = 0)) (PreH15 : (StrlenLittleEndian.valid_string m_capacity_spec )),
  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail_2)))) )
|--
  EX (tail: (@list Z)),
  “ (address = s_pre) ”
  &&  “ (0 = 0) ”
  &&  “ (0 <= s_pre) ”
  &&  “ ((s_pre % ( 8 ) ) = 0) ”
  &&  “ ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec) ”
  &&  “ (s_pre <= (unsigned_last_nbits ((p + 8 )) (64))) ”
  &&  “ ((unsigned_last_nbits ((p + 8 )) (64)) <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR)))) ”
  &&  “ (((unsigned_last_nbits ((p + 8 )) (64)) % ( 8 ) ) = 0) ”
  &&  “ (StrlenLittleEndian.valid_string m_capacity_spec ) ”
  &&  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
) \/
(
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (tail_2: (@list Z)) (p: Z) (start: Z) (address: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 >= 8)) (PreH2 : (sl_found retval start retval_2 )) (PreH3 : (sl_word_matches retval (app (m_capacity_spec) ((cons (0) (tail_2)))) ((sl_addr (p)) - s_pre ) )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= UINT64_MAX)) (PreH6 : (address = s_pre)) (PreH7 : (start = 0)) (PreH8 : (0 <= s_pre)) (PreH9 : ((s_pre % ( 8 ) ) = 0)) (PreH10 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)) (PreH12 : (s_pre <= p)) (PreH13 : (p <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR))))) (PreH14 : ((p % ( 8 ) ) = 0)) (PreH15 : (StrlenLittleEndian.valid_string m_capacity_spec )),
  TT && emp 
|--
  EX (tail: (@list Z)),
  “ ((app (m_capacity_spec) ((cons (0) (tail_2)))) = (app (m_capacity_spec) ((cons (0) (tail))))) ”
  &&  “ (s_pre <= (unsigned_last_nbits ((p + 8 )) (64))) ”
  &&  “ ((unsigned_last_nbits ((p + 8 )) (64)) <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR)))) ”
  &&  “ (((unsigned_last_nbits ((p + 8 )) (64)) % ( 8 ) ) = 0) ”
  &&  emp
).

Definition strlen_word_return_wit_1 :=
(
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (tail: (@list Z)) (p: Z) (start: Z) (address: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval < 8)) (PreH2 : (sl_found retval_2 start retval )) (PreH3 : (sl_word_matches retval_2 (app (m_capacity_spec) ((cons (0) (tail)))) ((sl_addr (p)) - s_pre ) )) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= UINT64_MAX)) (PreH6 : (address = s_pre)) (PreH7 : (start = 0)) (PreH8 : (0 <= s_pre)) (PreH9 : ((s_pre % ( 8 ) ) = 0)) (PreH10 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)) (PreH12 : (s_pre <= p)) (PreH13 : (p <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR))))) (PreH14 : ((p % ( 8 ) ) = 0)) (PreH15 : (StrlenLittleEndian.valid_string m_capacity_spec )),
  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits ((p + retval )) (64)) - address )) (64)) = (Zlength (m_capacity_spec))) ”
  &&  (ObjectString.store_string s_pre capacity_capacity_spec m_capacity_spec )
) \/
(
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (tail: (@list Z)) (p: Z) (start: Z) (address: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval < 8)) (PreH2 : (sl_found retval_2 start retval )) (PreH3 : (sl_word_matches retval_2 (app (m_capacity_spec) ((cons (0) (tail)))) ((sl_addr (p)) - s_pre ) )) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= UINT64_MAX)) (PreH6 : (address = s_pre)) (PreH7 : (start = 0)) (PreH8 : (0 <= s_pre)) (PreH9 : ((s_pre % ( 8 ) ) = 0)) (PreH10 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)) (PreH12 : (s_pre <= p)) (PreH13 : (p <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR))))) (PreH14 : ((p % ( 8 ) ) = 0)) (PreH15 : (StrlenLittleEndian.valid_string m_capacity_spec )),
  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits ((p + retval )) (64)) - s_pre )) (64)) = (Zlength (m_capacity_spec))) ”
  &&  (ObjectString.store_string s_pre capacity_capacity_spec m_capacity_spec )
).

Definition strlen_word_return_wit_1_split_goal_1 :=
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (tail: (@list Z)) (p: Z) (start: Z) (address: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval < 8)) (PreH2 : (sl_found retval_2 start retval )) (PreH3 : (sl_word_matches retval_2 (app (m_capacity_spec) ((cons (0) (tail)))) ((sl_addr (p)) - s_pre ) )) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= UINT64_MAX)) (PreH6 : (address = s_pre)) (PreH7 : (start = 0)) (PreH8 : (0 <= s_pre)) (PreH9 : ((s_pre % ( 8 ) ) = 0)) (PreH10 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)) (PreH12 : (s_pre <= p)) (PreH13 : (p <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR))))) (PreH14 : ((p % ( 8 ) ) = 0)) (PreH15 : (StrlenLittleEndian.valid_string m_capacity_spec )),
  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits ((p + retval )) (64)) - s_pre )) (64)) = (Zlength (m_capacity_spec))) ”
.

Definition strlen_word_return_wit_1_split_goal_spatial :=
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (tail: (@list Z)) (p: Z) (start: Z) (address: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval < 8)) (PreH2 : (sl_found retval_2 start retval )) (PreH3 : (sl_word_matches retval_2 (app (m_capacity_spec) ((cons (0) (tail)))) ((sl_addr (p)) - s_pre ) )) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= UINT64_MAX)) (PreH6 : (address = s_pre)) (PreH7 : (start = 0)) (PreH8 : (0 <= s_pre)) (PreH9 : ((s_pre % ( 8 ) ) = 0)) (PreH10 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH11 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)) (PreH12 : (s_pre <= p)) (PreH13 : (p <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR))))) (PreH14 : ((p % ( 8 ) ) = 0)) (PreH15 : (StrlenLittleEndian.valid_string m_capacity_spec )),
  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
|--
  (ObjectString.store_string s_pre capacity_capacity_spec m_capacity_spec )
.

Definition strlen_word_partial_solve_wit_1_pure :=
(
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (tail: (@list Z)) (p: Z) (start: Z) (address: Z) (PreH1 : (address = s_pre)) (PreH2 : (start = 0)) (PreH3 : (0 <= s_pre)) (PreH4 : ((s_pre % ( 8 ) ) = 0)) (PreH5 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH6 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)) (PreH7 : (s_pre <= p)) (PreH8 : (p <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR))))) (PreH9 : ((p % ( 8 ) ) = 0)) (PreH10 : (StrlenLittleEndian.valid_string m_capacity_spec )),
  ((( &( "w" ) )) # UInt64  |->_)
  **  ((( &( "address" ) )) # UInt64  |-> address)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "start" ) )) # UInt64  |-> start)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
|--
  “ (0 <= s_pre) ”
  &&  “ ((s_pre + capacity_capacity_spec ) <= UINT64_MAX) ”
  &&  “ (((sl_addr (p)) % ( 8 ) ) = 0) ”
  &&  “ (((sl_addr (p)) + 8 ) <= (s_pre + capacity_capacity_spec )) ”
  &&  “ (s_pre <= (sl_addr (p))) ”
) \/
(
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (tail: (@list Z)) (p: Z) (start: Z) (address: Z) (PreH1 : (p <= UINT64_MAX)) (PreH2 : (start <= UINT64_MAX)) (PreH3 : (address <= UINT64_MAX)) (PreH4 : (p >= 0)) (PreH5 : (start >= 0)) (PreH6 : (address >= 0)) (PreH7 : (address = s_pre)) (PreH8 : (start = 0)) (PreH9 : (0 <= s_pre)) (PreH10 : ((s_pre % ( 8 ) ) = 0)) (PreH11 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH12 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)) (PreH13 : (s_pre <= p)) (PreH14 : (p <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR))))) (PreH15 : ((p % ( 8 ) ) = 0)) (PreH16 : (StrlenLittleEndian.valid_string m_capacity_spec )),
  ((( &( "w" ) )) # UInt64  |->_)
  **  ((( &( "address" ) )) # UInt64  |-> address)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "start" ) )) # UInt64  |-> start)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
|--
  “ (s_pre <= (sl_addr (p))) ”
  &&  “ (((sl_addr (p)) + 8 ) <= (s_pre + capacity_capacity_spec )) ”
  &&  “ (((sl_addr (p)) % ( 8 ) ) = 0) ”
).

Definition strlen_word_partial_solve_wit_1_pure_split_goal_1 :=
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (tail: (@list Z)) (p: Z) (start: Z) (address: Z) (PreH1 : (p <= UINT64_MAX)) (PreH2 : (start <= UINT64_MAX)) (PreH3 : (address <= UINT64_MAX)) (PreH4 : (p >= 0)) (PreH5 : (start >= 0)) (PreH6 : (address >= 0)) (PreH7 : (address = s_pre)) (PreH8 : (start = 0)) (PreH9 : (0 <= s_pre)) (PreH10 : ((s_pre % ( 8 ) ) = 0)) (PreH11 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH12 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)) (PreH13 : (s_pre <= p)) (PreH14 : (p <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR))))) (PreH15 : ((p % ( 8 ) ) = 0)) (PreH16 : (StrlenLittleEndian.valid_string m_capacity_spec )),
  ((( &( "w" ) )) # UInt64  |->_)
  **  ((( &( "address" ) )) # UInt64  |-> address)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "start" ) )) # UInt64  |-> start)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
|--
  “ (s_pre <= (sl_addr (p))) ”
.

Definition strlen_word_partial_solve_wit_1_pure_split_goal_2 :=
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (tail: (@list Z)) (p: Z) (start: Z) (address: Z) (PreH1 : (p <= UINT64_MAX)) (PreH2 : (start <= UINT64_MAX)) (PreH3 : (address <= UINT64_MAX)) (PreH4 : (p >= 0)) (PreH5 : (start >= 0)) (PreH6 : (address >= 0)) (PreH7 : (address = s_pre)) (PreH8 : (start = 0)) (PreH9 : (0 <= s_pre)) (PreH10 : ((s_pre % ( 8 ) ) = 0)) (PreH11 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH12 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)) (PreH13 : (s_pre <= p)) (PreH14 : (p <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR))))) (PreH15 : ((p % ( 8 ) ) = 0)) (PreH16 : (StrlenLittleEndian.valid_string m_capacity_spec )),
  ((( &( "w" ) )) # UInt64  |->_)
  **  ((( &( "address" ) )) # UInt64  |-> address)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "start" ) )) # UInt64  |-> start)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
|--
  “ (((sl_addr (p)) + 8 ) <= (s_pre + capacity_capacity_spec )) ”
.

Definition strlen_word_partial_solve_wit_1_pure_split_goal_3 :=
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (tail: (@list Z)) (p: Z) (start: Z) (address: Z) (PreH1 : (p <= UINT64_MAX)) (PreH2 : (start <= UINT64_MAX)) (PreH3 : (address <= UINT64_MAX)) (PreH4 : (p >= 0)) (PreH5 : (start >= 0)) (PreH6 : (address >= 0)) (PreH7 : (address = s_pre)) (PreH8 : (start = 0)) (PreH9 : (0 <= s_pre)) (PreH10 : ((s_pre % ( 8 ) ) = 0)) (PreH11 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH12 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)) (PreH13 : (s_pre <= p)) (PreH14 : (p <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR))))) (PreH15 : ((p % ( 8 ) ) = 0)) (PreH16 : (StrlenLittleEndian.valid_string m_capacity_spec )),
  ((( &( "w" ) )) # UInt64  |->_)
  **  ((( &( "address" ) )) # UInt64  |-> address)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "start" ) )) # UInt64  |-> start)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
|--
  “ (((sl_addr (p)) % ( 8 ) ) = 0) ”
.

Definition strlen_word_partial_solve_wit_1_aux :=
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (tail: (@list Z)) (p: Z) (start: Z) (address: Z) (PreH1 : (address = s_pre)) (PreH2 : (start = 0)) (PreH3 : (0 <= s_pre)) (PreH4 : ((s_pre % ( 8 ) ) = 0)) (PreH5 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH6 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)) (PreH7 : (s_pre <= p)) (PreH8 : (p <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR))))) (PreH9 : ((p % ( 8 ) ) = 0)) (PreH10 : (StrlenLittleEndian.valid_string m_capacity_spec )),
  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
|--
  “ (0 <= s_pre) ”
  &&  “ ((s_pre + capacity_capacity_spec ) <= UINT64_MAX) ”
  &&  “ (((sl_addr (p)) % ( 8 ) ) = 0) ”
  &&  “ (((sl_addr (p)) + 8 ) <= (s_pre + capacity_capacity_spec )) ”
  &&  “ (s_pre <= (sl_addr (p))) ”
  &&  “ (address = s_pre) ”
  &&  “ (start = 0) ”
  &&  “ (0 <= s_pre) ”
  &&  “ ((s_pre % ( 8 ) ) = 0) ”
  &&  “ ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec) ”
  &&  “ (s_pre <= p) ”
  &&  “ (p <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR)))) ”
  &&  “ ((p % ( 8 ) ) = 0) ”
  &&  “ (StrlenLittleEndian.valid_string m_capacity_spec ) ”
  &&  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
.

Definition strlen_word_partial_solve_wit_1 := strlen_word_partial_solve_wit_1_pure -> strlen_word_partial_solve_wit_1_aux.

Definition strlen_word_partial_solve_wit_2_pure :=
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (tail: (@list Z)) (p: Z) (start: Z) (address: Z) (retval: Z) (PreH1 : (sl_word_matches retval (app (m_capacity_spec) ((cons (0) (tail)))) ((sl_addr (p)) - s_pre ) )) (PreH2 : (0 <= retval)) (PreH3 : (retval <= UINT64_MAX)) (PreH4 : (address = s_pre)) (PreH5 : (start = 0)) (PreH6 : (0 <= s_pre)) (PreH7 : ((s_pre % ( 8 ) ) = 0)) (PreH8 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH9 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)) (PreH10 : (s_pre <= p)) (PreH11 : (p <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR))))) (PreH12 : ((p % ( 8 ) ) = 0)) (PreH13 : (StrlenLittleEndian.valid_string m_capacity_spec )),
  ((( &( "k" ) )) # UInt64  |->_)
  **  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
  **  ((( &( "w" ) )) # UInt64  |-> retval)
  **  ((( &( "address" ) )) # UInt64  |-> address)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "start" ) )) # UInt64  |-> start)
  **  ((( &( "p" ) )) # UInt64  |-> p)
|--
  “ (0 <= start) ”
  &&  “ (start < 8) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval <= UINT64_MAX) ”
.

Definition strlen_word_partial_solve_wit_2_aux :=
forall (m_capacity_spec: (@list Z)) (capacity_capacity_spec: Z) (s_pre: Z) (tail: (@list Z)) (p: Z) (start: Z) (address: Z) (retval: Z) (PreH1 : (sl_word_matches retval (app (m_capacity_spec) ((cons (0) (tail)))) ((sl_addr (p)) - s_pre ) )) (PreH2 : (0 <= retval)) (PreH3 : (retval <= UINT64_MAX)) (PreH4 : (address = s_pre)) (PreH5 : (start = 0)) (PreH6 : (0 <= s_pre)) (PreH7 : ((s_pre % ( 8 ) ) = 0)) (PreH8 : ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX)) (PreH9 : ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec)) (PreH10 : (s_pre <= p)) (PreH11 : (p <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR))))) (PreH12 : ((p % ( 8 ) ) = 0)) (PreH13 : (StrlenLittleEndian.valid_string m_capacity_spec )),
  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
|--
  “ (0 <= start) ”
  &&  “ (start < 8) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval <= UINT64_MAX) ”
  &&  “ (sl_word_matches retval (app (m_capacity_spec) ((cons (0) (tail)))) ((sl_addr (p)) - s_pre ) ) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval <= UINT64_MAX) ”
  &&  “ (address = s_pre) ”
  &&  “ (start = 0) ”
  &&  “ (0 <= s_pre) ”
  &&  “ ((s_pre % ( 8 ) ) = 0) ”
  &&  “ ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec) ”
  &&  “ (s_pre <= p) ”
  &&  “ (p <= (s_pre + ((Zlength (m_capacity_spec)) * sizeof(UCHAR)))) ”
  &&  “ ((p % ( 8 ) ) = 0) ”
  &&  “ (StrlenLittleEndian.valid_string m_capacity_spec ) ”
  &&  (UCharArray.full s_pre capacity_capacity_spec (app (m_capacity_spec) ((cons (0) (tail)))) )
.

Definition strlen_word_partial_solve_wit_2 := strlen_word_partial_solve_wit_2_pure -> strlen_word_partial_solve_wit_2_aux.

(* Shallow FunAssertion specs for strlen_word. *)
Definition strlen_word_sig : FuncSig := ([ * u8], u64)%ctype.

Definition strlen_word_capacity_spec : Spec strlen_word_sig :=
  fun F =>
ALL (capacity: Z),
ALL (m: (@list Z)),
HoareFun ([ * u8], u64)%ctype
  (fun s_pre =>
  (“ (0 <= s_pre) ”
  &&  “ ((s_pre % ( 8 ) ) = 0) ”
  &&  “ ((s_pre + (capacity * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ ((8 * (((Zlength (m)) ÷ 8 ) + 1 ) ) <= capacity) ”
  &&  (ObjectString.store_string s_pre capacity m )))
  (fun s_pre retval =>
  (“ (retval = (Zlength (m))) ”
  &&  (ObjectString.store_string s_pre capacity m )))
  F.

Definition strlen_word_exact_spec : Spec strlen_word_sig :=
  fun F =>
ALL (m: (@list Z)),
HoareFun ([ * u8], u64)%ctype
  (fun s_pre =>
  (“ (0 <= s_pre) ”
  &&  “ ((s_pre % ( 8 ) ) = 0) ”
  &&  “ ((s_pre + (((Zlength (m)) + 1 ) * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ ((8 * (((Zlength (m)) ÷ 8 ) + 1 ) ) <= ((Zlength (m)) + 1 )) ”
  &&  (ObjectString.store_string_exact s_pre m )))
  (fun s_pre retval =>
  (“ (retval = (Zlength (m))) ”
  &&  (ObjectString.store_string_exact s_pre m )))
  F.

Definition strlen_word_capacity_spec_entail_exact_spec :=
forall (s_pre: Z) (m_exact_spec: (@list Z)),
  (“ (0 <= s_pre) ”
  &&  “ ((s_pre % ( 8 ) ) = 0) ”
  &&  “ ((s_pre + (((Zlength (m_exact_spec)) + 1 ) * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ ((8 * (((Zlength (m_exact_spec)) ÷ 8 ) + 1 ) ) <= ((Zlength (m_exact_spec)) + 1 )) ”
  &&  (ObjectString.store_string_exact s_pre m_exact_spec ))
|--
EX (capacity_capacity_spec: Z)(m_capacity_spec: (@list Z)),
  (“ (0 <= s_pre) ”
  &&  “ ((s_pre % ( 8 ) ) = 0) ”
  &&  “ ((s_pre + (capacity_capacity_spec * sizeof(UCHAR))) <= UINT64_MAX) ”
  &&  “ ((8 * (((Zlength (m_capacity_spec)) ÷ 8 ) + 1 ) ) <= capacity_capacity_spec) ”
  &&  (ObjectString.store_string s_pre capacity_capacity_spec m_capacity_spec ))
  **
  (ALL (retval: Z),
  (“ (retval = (Zlength (m_capacity_spec))) ”
  &&  (ObjectString.store_string s_pre capacity_capacity_spec m_capacity_spec ))
  -*
  (“ (retval = (Zlength (m_exact_spec))) ”
  &&  (ObjectString.store_string_exact s_pre m_exact_spec )))
.

Module Type VC_Correct.


Axiom proof_of_sl_load_word_entail_wit_1 : sl_load_word_entail_wit_1.
Axiom proof_of_sl_load_word_return_wit_1 : sl_load_word_return_wit_1.
Axiom proof_of_sl_first_zero_safety_wit_1 : sl_first_zero_safety_wit_1.
Axiom proof_of_sl_first_zero_safety_wit_2 : sl_first_zero_safety_wit_2.
Axiom proof_of_sl_first_zero_safety_wit_3 : sl_first_zero_safety_wit_3.
Axiom proof_of_sl_first_zero_safety_wit_4 : sl_first_zero_safety_wit_4.
Axiom proof_of_sl_first_zero_safety_wit_5 : sl_first_zero_safety_wit_5.
Axiom proof_of_sl_first_zero_safety_wit_6 : sl_first_zero_safety_wit_6.
Axiom proof_of_sl_first_zero_safety_wit_7 : sl_first_zero_safety_wit_7.
Axiom proof_of_sl_first_zero_safety_wit_8 : sl_first_zero_safety_wit_8.
Axiom proof_of_sl_first_zero_safety_wit_9 : sl_first_zero_safety_wit_9.
Axiom proof_of_sl_first_zero_safety_wit_10 : sl_first_zero_safety_wit_10.
Axiom proof_of_sl_first_zero_entail_wit_1 : sl_first_zero_entail_wit_1.
Axiom proof_of_sl_first_zero_entail_wit_2 : sl_first_zero_entail_wit_2.
Axiom proof_of_sl_first_zero_entail_wit_3 : sl_first_zero_entail_wit_3.
Axiom proof_of_sl_first_zero_entail_wit_4 : sl_first_zero_entail_wit_4.
Axiom proof_of_sl_first_zero_return_wit_1 : sl_first_zero_return_wit_1.
Axiom proof_of_sl_first_zero_return_wit_2 : sl_first_zero_return_wit_2.
Axiom proof_of_strlen_word_safety_wit_1 : strlen_word_safety_wit_1.
Axiom proof_of_strlen_word_safety_wit_2 : strlen_word_safety_wit_2.
Axiom proof_of_strlen_word_safety_wit_3 : strlen_word_safety_wit_3.
Axiom proof_of_strlen_word_safety_wit_4 : strlen_word_safety_wit_4.
Axiom proof_of_strlen_word_safety_wit_5 : strlen_word_safety_wit_5.
Axiom proof_of_strlen_word_safety_wit_6 : strlen_word_safety_wit_6.
Axiom proof_of_strlen_word_entail_wit_1 : strlen_word_entail_wit_1.
Axiom proof_of_strlen_word_entail_wit_2 : strlen_word_entail_wit_2.
Axiom proof_of_strlen_word_return_wit_1 : strlen_word_return_wit_1.
Axiom proof_of_strlen_word_partial_solve_wit_1_pure : strlen_word_partial_solve_wit_1_pure.
Axiom proof_of_strlen_word_partial_solve_wit_1 : strlen_word_partial_solve_wit_1.
Axiom proof_of_strlen_word_partial_solve_wit_2_pure : strlen_word_partial_solve_wit_2_pure.
Axiom proof_of_strlen_word_partial_solve_wit_2 : strlen_word_partial_solve_wit_2.
Axiom proof_of_strlen_word_capacity_spec_entail_exact_spec : strlen_word_capacity_spec_entail_exact_spec.

End VC_Correct.
