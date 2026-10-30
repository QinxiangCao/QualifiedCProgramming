From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P048_1607E_robot_on_the_board_1_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85)))),
  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_full row_pre 1 )
  **  (IntArray.undef_full col_pre 1 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85)))),
  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_full row_pre 1 )
  **  (IntArray.undef_full col_pre 1 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85)))),
  ((( &( "maxc" ) )) # Int  |->_)
  **  ((( &( "minc" ) )) # Int  |-> 0)
  **  ((( &( "maxr" ) )) # Int  |-> 0)
  **  ((( &( "minr" ) )) # Int  |-> 0)
  **  ((( &( "c" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_full row_pre 1 )
  **  (IntArray.undef_full col_pre 1 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85)))),
  ((( &( "minc" ) )) # Int  |->_)
  **  ((( &( "maxr" ) )) # Int  |-> 0)
  **  ((( &( "minr" ) )) # Int  |-> 0)
  **  ((( &( "c" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_full row_pre 1 )
  **  (IntArray.undef_full col_pre 1 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85)))),
  ((( &( "maxr" ) )) # Int  |->_)
  **  ((( &( "minr" ) )) # Int  |-> 0)
  **  ((( &( "c" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_full row_pre 1 )
  **  (IntArray.undef_full col_pre 1 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85)))),
  ((( &( "minr" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_full row_pre 1 )
  **  (IntArray.undef_full col_pre 1 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85)))),
  ((( &( "bc" ) )) # Int  |->_)
  **  ((( &( "br" ) )) # Int  |-> 0)
  **  ((( &( "maxc" ) )) # Int  |-> 0)
  **  ((( &( "minc" ) )) # Int  |-> 0)
  **  ((( &( "maxr" ) )) # Int  |-> 0)
  **  ((( &( "minr" ) )) # Int  |-> 0)
  **  ((( &( "c" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_full row_pre 1 )
  **  (IntArray.undef_full col_pre 1 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85)))),
  ((( &( "br" ) )) # Int  |->_)
  **  ((( &( "maxc" ) )) # Int  |-> 0)
  **  ((( &( "minc" ) )) # Int  |-> 0)
  **  ((( &( "maxr" ) )) # Int  |-> 0)
  **  ((( &( "minr" ) )) # Int  |-> 0)
  **  ((( &( "c" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_full row_pre 1 )
  **  (IntArray.undef_full col_pre 1 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85)))),
  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((row_pre) # Int  |->_)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((col_pre) # Int  |->_)
  **  ((( &( "bc" ) )) # Int  |-> 0)
  **  ((( &( "br" ) )) # Int  |-> 0)
  **  ((( &( "maxc" ) )) # Int  |-> 0)
  **  ((( &( "minc" ) )) # Int  |-> 0)
  **  ((( &( "maxr" ) )) # Int  |-> 0)
  **  ((( &( "minr" ) )) # Int  |-> 0)
  **  ((( &( "c" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
|--
  “ ((1 - 0 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (1 - 0 )) ”
.

Definition solver_safety_wit_10 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85)))),
  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((row_pre) # Int  |->_)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((col_pre) # Int  |->_)
  **  ((( &( "bc" ) )) # Int  |-> 0)
  **  ((( &( "br" ) )) # Int  |-> 0)
  **  ((( &( "maxc" ) )) # Int  |-> 0)
  **  ((( &( "minc" ) )) # Int  |-> 0)
  **  ((( &( "maxr" ) )) # Int  |-> 0)
  **  ((( &( "minr" ) )) # Int  |-> 0)
  **  ((( &( "c" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_11 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85)))),
  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((row_pre) # Int  |-> (1 - 0 ))
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((col_pre) # Int  |->_)
  **  ((( &( "bc" ) )) # Int  |-> 0)
  **  ((( &( "br" ) )) # Int  |-> 0)
  **  ((( &( "maxc" ) )) # Int  |-> 0)
  **  ((( &( "minc" ) )) # Int  |-> 0)
  **  ((( &( "maxr" ) )) # Int  |-> 0)
  **  ((( &( "minr" ) )) # Int  |-> 0)
  **  ((( &( "c" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
|--
  “ ((1 - 0 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (1 - 0 )) ”
.

Definition solver_safety_wit_12 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85)))),
  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((row_pre) # Int  |-> (1 - 0 ))
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((col_pre) # Int  |->_)
  **  ((( &( "bc" ) )) # Int  |-> 0)
  **  ((( &( "br" ) )) # Int  |-> 0)
  **  ((( &( "maxc" ) )) # Int  |-> 0)
  **  ((( &( "minc" ) )) # Int  |-> 0)
  **  ((( &( "maxr" ) )) # Int  |-> 0)
  **  ((( &( "minr" ) )) # Int  |-> 0)
  **  ((( &( "c" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_13 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((row_pre) # Int  |-> (1 - 0 ))
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((col_pre) # Int  |-> (1 - 0 ))
  **  ((( &( "bc" ) )) # Int  |-> 0)
  **  ((( &( "br" ) )) # Int  |-> 0)
  **  ((( &( "maxc" ) )) # Int  |-> 0)
  **  ((( &( "minc" ) )) # Int  |-> 0)
  **  ((( &( "maxr" ) )) # Int  |-> 0)
  **  ((( &( "minr" ) )) # Int  |-> 0)
  **  ((( &( "c" ) )) # Int  |-> 0)
  **  ((( &( "r" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_14 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= 0)) (PreH16 : (0 <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= 0)) (PreH20 : (0 <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = 0)) (PreH23 : (bc = 0)) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH26 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ (85 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 85) ”
.

Definition solver_safety_wit_15 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= 0)) (PreH16 : (0 <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= 0)) (PreH20 : (0 <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = 0)) (PreH23 : (bc = 0)) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH26 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH27 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ ((r - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r - 1 )) ”
.

Definition solver_safety_wit_16 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= 0)) (PreH16 : (0 <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= 0)) (PreH20 : (0 <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = 0)) (PreH23 : (bc = 0)) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH26 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH27 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ (68 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 68) ”
.

Definition solver_safety_wit_17 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= 0)) (PreH16 : (0 <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= 0)) (PreH20 : (0 <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = 0)) (PreH23 : (bc = 0)) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH26 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH27 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH28 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ ((r + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition solver_safety_wit_18 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= 0)) (PreH16 : (0 <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= 0)) (PreH20 : (0 <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = 0)) (PreH23 : (bc = 0)) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH26 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH27 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH28 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ (76 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 76) ”
.

Definition solver_safety_wit_19 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= 0)) (PreH16 : (0 <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= 0)) (PreH20 : (0 <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = 0)) (PreH23 : (bc = 0)) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH26 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH27 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH28 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH29 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ ((c - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (c - 1 )) ”
.

Definition solver_safety_wit_20 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= 0)) (PreH16 : (0 <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= 0)) (PreH20 : (0 <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = 0)) (PreH23 : (bc = 0)) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH26 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH27 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH28 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH29 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ ((c + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (c + 1 )) ”
.

Definition solver_safety_wit_21 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((r - 1 ) > maxr)) (PreH2 : ((r - 1 ) < minr)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH10 : (0 <= i)) (PreH11 : (i <= (Zlength (moves)))) (PreH12 : ((-i) <= r)) (PreH13 : (r <= i)) (PreH14 : ((-i) <= c)) (PreH15 : (c <= i)) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= 0)) (PreH18 : (0 <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= 0)) (PreH22 : (0 <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : (br = 0)) (PreH25 : (bc = 0)) (PreH26 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH27 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH28 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH29 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  ((( &( "nmaxr" ) )) # Int  |->_)
  **  ((( &( "nminr" ) )) # Int  |-> (r - 1 ))
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ False ”
.

Definition solver_safety_wit_22 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((r + 1 ) > maxr)) (PreH2 : ((r + 1 ) < minr)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH10 : (0 <= i)) (PreH11 : (i <= (Zlength (moves)))) (PreH12 : ((-i) <= r)) (PreH13 : (r <= i)) (PreH14 : ((-i) <= c)) (PreH15 : (c <= i)) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= 0)) (PreH18 : (0 <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= 0)) (PreH22 : (0 <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : (br = 0)) (PreH25 : (bc = 0)) (PreH26 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH27 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH28 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH29 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH30 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  ((( &( "nmaxr" ) )) # Int  |->_)
  **  ((( &( "nminr" ) )) # Int  |-> (r + 1 ))
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> (r + 1 ))
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ False ”
.

Definition solver_safety_wit_23 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (r > maxr)) (PreH2 : (r < minr)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH10 : (0 <= i)) (PreH11 : (i <= (Zlength (moves)))) (PreH12 : ((-i) <= r)) (PreH13 : (r <= i)) (PreH14 : ((-i) <= c)) (PreH15 : (c <= i)) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= 0)) (PreH18 : (0 <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= 0)) (PreH22 : (0 <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : (br = 0)) (PreH25 : (bc = 0)) (PreH26 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH27 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH28 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH29 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH30 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH31 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  ((( &( "nmaxr" ) )) # Int  |->_)
  **  ((( &( "nminr" ) )) # Int  |-> r)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> (c - 1 ))
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ False ”
.

Definition solver_safety_wit_24 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (r > maxr)) (PreH2 : (r < minr)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH10 : (0 <= i)) (PreH11 : (i <= (Zlength (moves)))) (PreH12 : ((-i) <= r)) (PreH13 : (r <= i)) (PreH14 : ((-i) <= c)) (PreH15 : (c <= i)) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= 0)) (PreH18 : (0 <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= 0)) (PreH22 : (0 <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : (br = 0)) (PreH25 : (bc = 0)) (PreH26 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH27 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH28 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH29 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH30 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH31 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  ((( &( "nmaxr" ) )) # Int  |->_)
  **  ((( &( "nminr" ) )) # Int  |-> r)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> (c + 1 ))
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ False ”
.

Definition solver_safety_wit_25 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  ((( &( "nmaxc" ) )) # Int  |->_)
  **  ((( &( "nminc" ) )) # Int  |-> c)
  **  ((( &( "nmaxr" ) )) # Int  |-> maxr)
  **  ((( &( "nminr" ) )) # Int  |-> (r - 1 ))
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ False ”
.

Definition solver_safety_wit_26 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1 ) > maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  ((( &( "nmaxc" ) )) # Int  |->_)
  **  ((( &( "nminc" ) )) # Int  |-> c)
  **  ((( &( "nmaxr" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "nminr" ) )) # Int  |-> minr)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ False ”
.

Definition solver_safety_wit_27 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  ((( &( "nmaxc" ) )) # Int  |->_)
  **  ((( &( "nminc" ) )) # Int  |-> c)
  **  ((( &( "nmaxr" ) )) # Int  |-> maxr)
  **  ((( &( "nminr" ) )) # Int  |-> minr)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> (r - 1 ))
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ False ”
.

Definition solver_safety_wit_28 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  ((( &( "nmaxc" ) )) # Int  |->_)
  **  ((( &( "nminc" ) )) # Int  |-> c)
  **  ((( &( "nmaxr" ) )) # Int  |-> maxr)
  **  ((( &( "nminr" ) )) # Int  |-> (r + 1 ))
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> (r + 1 ))
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ False ”
.

Definition solver_safety_wit_29 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1 ) > maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  ((( &( "nmaxc" ) )) # Int  |->_)
  **  ((( &( "nminc" ) )) # Int  |-> c)
  **  ((( &( "nmaxr" ) )) # Int  |-> (r + 1 ))
  **  ((( &( "nminr" ) )) # Int  |-> minr)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> (r + 1 ))
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ False ”
.

Definition solver_safety_wit_30 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  ((( &( "nmaxc" ) )) # Int  |->_)
  **  ((( &( "nminc" ) )) # Int  |-> c)
  **  ((( &( "nmaxr" ) )) # Int  |-> maxr)
  **  ((( &( "nminr" ) )) # Int  |-> minr)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> (r + 1 ))
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ False ”
.

Definition solver_safety_wit_31 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) > maxc)) (PreH2 : ((c - 1 ) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  ((( &( "nmaxc" ) )) # Int  |->_)
  **  ((( &( "nminc" ) )) # Int  |-> (c - 1 ))
  **  ((( &( "nmaxr" ) )) # Int  |-> maxr)
  **  ((( &( "nminr" ) )) # Int  |-> r)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> (c - 1 ))
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ False ”
.

Definition solver_safety_wit_32 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) > maxc)) (PreH2 : ((c - 1 ) < minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  ((( &( "nmaxc" ) )) # Int  |->_)
  **  ((( &( "nminc" ) )) # Int  |-> (c - 1 ))
  **  ((( &( "nmaxr" ) )) # Int  |-> r)
  **  ((( &( "nminr" ) )) # Int  |-> minr)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> (c - 1 ))
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ False ”
.

Definition solver_safety_wit_33 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) > maxc)) (PreH2 : ((c - 1 ) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  ((( &( "nmaxc" ) )) # Int  |->_)
  **  ((( &( "nminc" ) )) # Int  |-> (c - 1 ))
  **  ((( &( "nmaxr" ) )) # Int  |-> maxr)
  **  ((( &( "nminr" ) )) # Int  |-> minr)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> (c - 1 ))
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ False ”
.

Definition solver_safety_wit_34 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) > maxc)) (PreH2 : ((c + 1 ) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  ((( &( "nmaxc" ) )) # Int  |->_)
  **  ((( &( "nminc" ) )) # Int  |-> (c + 1 ))
  **  ((( &( "nmaxr" ) )) # Int  |-> maxr)
  **  ((( &( "nminr" ) )) # Int  |-> r)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> (c + 1 ))
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ False ”
.

Definition solver_safety_wit_35 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) > maxc)) (PreH2 : ((c + 1 ) < minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  ((( &( "nmaxc" ) )) # Int  |->_)
  **  ((( &( "nminc" ) )) # Int  |-> (c + 1 ))
  **  ((( &( "nmaxr" ) )) # Int  |-> r)
  **  ((( &( "nminr" ) )) # Int  |-> minr)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> (c + 1 ))
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ False ”
.

Definition solver_safety_wit_36 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) > maxc)) (PreH2 : ((c + 1 ) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  ((( &( "nmaxc" ) )) # Int  |->_)
  **  ((( &( "nminc" ) )) # Int  |-> (c + 1 ))
  **  ((( &( "nmaxr" ) )) # Int  |-> maxr)
  **  ((( &( "nminr" ) )) # Int  |-> minr)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> (c + 1 ))
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ False ”
.

Definition solver_safety_wit_37 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (oldr: Z) (oldc: Z) (i: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (nminr: Z) (nmaxr: Z) (nminc: Z) (nmaxc: Z) (br: Z) (bc: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH8 : (0 <= i)) (PreH9 : (i < (Zlength (moves)))) (PreH10 : ((-(i + 1 )) <= r)) (PreH11 : (r <= (i + 1 ))) (PreH12 : ((-(i + 1 )) <= c)) (PreH13 : (c <= (i + 1 ))) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= 0)) (PreH16 : (0 <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= 0)) (PreH20 : (0 <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : ((-(i + 1 )) <= nminr)) (PreH23 : (nminr <= 0)) (PreH24 : (0 <= nmaxr)) (PreH25 : (nmaxr <= (i + 1 ))) (PreH26 : ((-(i + 1 )) <= nminc)) (PreH27 : (nminc <= 0)) (PreH28 : (0 <= nmaxc)) (PreH29 : (nmaxc <= (i + 1 ))) (PreH30 : (br = 0)) (PreH31 : (bc = 0)) (PreH32 : (PrefixWindow moves i oldr oldc minr maxr minc maxc )) (PreH33 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH34 : (PrefixWindow moves (i + 1 ) r c nminr nmaxr nminc nmaxc )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "nminr" ) )) # Int  |-> nminr)
  **  ((( &( "nmaxr" ) )) # Int  |-> nmaxr)
  **  ((( &( "nminc" ) )) # Int  |-> nminc)
  **  ((( &( "nmaxc" ) )) # Int  |-> nmaxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ ((nmaxr - nminr ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (nmaxr - nminr )) ”
.

Definition solver_safety_wit_38 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (oldr: Z) (oldc: Z) (i: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (nminr: Z) (nmaxr: Z) (nminc: Z) (nmaxc: Z) (br: Z) (bc: Z) (PreH1 : ((nmaxr - nminr ) < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000)) (PreH6 : (1 <= (Zlength (moves)))) (PreH7 : ((Zlength (moves)) <= 1000000)) (PreH8 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength (moves)))) (PreH11 : ((-(i + 1 )) <= r)) (PreH12 : (r <= (i + 1 ))) (PreH13 : ((-(i + 1 )) <= c)) (PreH14 : (c <= (i + 1 ))) (PreH15 : ((-i) <= minr)) (PreH16 : (minr <= 0)) (PreH17 : (0 <= maxr)) (PreH18 : (maxr <= i)) (PreH19 : ((-i) <= minc)) (PreH20 : (minc <= 0)) (PreH21 : (0 <= maxc)) (PreH22 : (maxc <= i)) (PreH23 : ((-(i + 1 )) <= nminr)) (PreH24 : (nminr <= 0)) (PreH25 : (0 <= nmaxr)) (PreH26 : (nmaxr <= (i + 1 ))) (PreH27 : ((-(i + 1 )) <= nminc)) (PreH28 : (nminc <= 0)) (PreH29 : (0 <= nmaxc)) (PreH30 : (nmaxc <= (i + 1 ))) (PreH31 : (br = 0)) (PreH32 : (bc = 0)) (PreH33 : (PrefixWindow moves i oldr oldc minr maxr minc maxc )) (PreH34 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH35 : (PrefixWindow moves (i + 1 ) r c nminr nmaxr nminc nmaxc )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "nminr" ) )) # Int  |-> nminr)
  **  ((( &( "nmaxr" ) )) # Int  |-> nmaxr)
  **  ((( &( "nminc" ) )) # Int  |-> nminc)
  **  ((( &( "nmaxc" ) )) # Int  |-> nmaxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ ((nmaxc - nminc ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (nmaxc - nminc )) ”
.

Definition solver_safety_wit_39 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (oldr: Z) (oldc: Z) (i: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (nminr: Z) (nmaxr: Z) (nminc: Z) (nmaxc: Z) (br: Z) (bc: Z) (PreH1 : ((nmaxc - nminc ) < m_pre)) (PreH2 : ((nmaxr - nminr ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength (moves)))) (PreH12 : ((-(i + 1 )) <= r)) (PreH13 : (r <= (i + 1 ))) (PreH14 : ((-(i + 1 )) <= c)) (PreH15 : (c <= (i + 1 ))) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= 0)) (PreH18 : (0 <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= 0)) (PreH22 : (0 <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : ((-(i + 1 )) <= nminr)) (PreH25 : (nminr <= 0)) (PreH26 : (0 <= nmaxr)) (PreH27 : (nmaxr <= (i + 1 ))) (PreH28 : ((-(i + 1 )) <= nminc)) (PreH29 : (nminc <= 0)) (PreH30 : (0 <= nmaxc)) (PreH31 : (nmaxc <= (i + 1 ))) (PreH32 : (br = 0)) (PreH33 : (bc = 0)) (PreH34 : (PrefixWindow moves i oldr oldc minr maxr minc maxc )) (PreH35 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH36 : (PrefixWindow moves (i + 1 ) r c nminr nmaxr nminc nmaxc )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> nminr)
  **  ((( &( "maxr" ) )) # Int  |-> nmaxr)
  **  ((( &( "minc" ) )) # Int  |-> nminc)
  **  ((( &( "maxc" ) )) # Int  |-> nmaxc)
  **  ((( &( "br" ) )) # Int  |-> br)
  **  ((( &( "bc" ) )) # Int  |-> bc)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_40 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (br: Z) (bc: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH8 : ((-(Zlength (moves))) <= r)) (PreH9 : (r <= (Zlength (moves)))) (PreH10 : ((-(Zlength (moves))) <= c)) (PreH11 : (c <= (Zlength (moves)))) (PreH12 : ((-(Zlength (moves))) <= minr)) (PreH13 : (minr <= 0)) (PreH14 : (0 <= maxr)) (PreH15 : (maxr <= (Zlength (moves)))) (PreH16 : ((-(Zlength (moves))) <= minc)) (PreH17 : (minc <= 0)) (PreH18 : (0 <= maxc)) (PreH19 : (maxc <= (Zlength (moves)))) (PreH20 : (br = 0)) (PreH21 : (bc = 0)) (PreH22 : (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc )),
  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((row_pre) # Int  |-> 1)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((col_pre) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> minr)
  **  ((( &( "bc" ) )) # Int  |-> minc)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
|--
  “ ((1 - minr ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (1 - minr )) ”
.

Definition solver_safety_wit_41 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (br: Z) (bc: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH8 : ((-(Zlength (moves))) <= r)) (PreH9 : (r <= (Zlength (moves)))) (PreH10 : ((-(Zlength (moves))) <= c)) (PreH11 : (c <= (Zlength (moves)))) (PreH12 : ((-(Zlength (moves))) <= minr)) (PreH13 : (minr <= 0)) (PreH14 : (0 <= maxr)) (PreH15 : (maxr <= (Zlength (moves)))) (PreH16 : ((-(Zlength (moves))) <= minc)) (PreH17 : (minc <= 0)) (PreH18 : (0 <= maxc)) (PreH19 : (maxc <= (Zlength (moves)))) (PreH20 : (br = 0)) (PreH21 : (bc = 0)) (PreH22 : (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc )),
  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((row_pre) # Int  |-> 1)
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((col_pre) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> minr)
  **  ((( &( "bc" ) )) # Int  |-> minc)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_42 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (br: Z) (bc: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH8 : ((-(Zlength (moves))) <= r)) (PreH9 : (r <= (Zlength (moves)))) (PreH10 : ((-(Zlength (moves))) <= c)) (PreH11 : (c <= (Zlength (moves)))) (PreH12 : ((-(Zlength (moves))) <= minr)) (PreH13 : (minr <= 0)) (PreH14 : (0 <= maxr)) (PreH15 : (maxr <= (Zlength (moves)))) (PreH16 : ((-(Zlength (moves))) <= minc)) (PreH17 : (minc <= 0)) (PreH18 : (0 <= maxc)) (PreH19 : (maxc <= (Zlength (moves)))) (PreH20 : (br = 0)) (PreH21 : (bc = 0)) (PreH22 : (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc )),
  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((row_pre) # Int  |-> (1 - minr ))
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((col_pre) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> minr)
  **  ((( &( "bc" ) )) # Int  |-> minc)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
|--
  “ ((1 - minc ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (1 - minc )) ”
.

Definition solver_safety_wit_43 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (br: Z) (bc: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH8 : ((-(Zlength (moves))) <= r)) (PreH9 : (r <= (Zlength (moves)))) (PreH10 : ((-(Zlength (moves))) <= c)) (PreH11 : (c <= (Zlength (moves)))) (PreH12 : ((-(Zlength (moves))) <= minr)) (PreH13 : (minr <= 0)) (PreH14 : (0 <= maxr)) (PreH15 : (maxr <= (Zlength (moves)))) (PreH16 : ((-(Zlength (moves))) <= minc)) (PreH17 : (minc <= 0)) (PreH18 : (0 <= maxc)) (PreH19 : (maxc <= (Zlength (moves)))) (PreH20 : (br = 0)) (PreH21 : (bc = 0)) (PreH22 : (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc )),
  ((( &( "row" ) )) # Ptr  |-> row_pre)
  **  ((row_pre) # Int  |-> (1 - minr ))
  **  ((( &( "col" ) )) # Ptr  |-> col_pre)
  **  ((col_pre) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "minr" ) )) # Int  |-> minr)
  **  ((( &( "maxr" ) )) # Int  |-> maxr)
  **  ((( &( "minc" ) )) # Int  |-> minc)
  **  ((( &( "maxc" ) )) # Int  |-> maxc)
  **  ((( &( "br" ) )) # Int  |-> minr)
  **  ((( &( "bc" ) )) # Int  |-> minc)
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85)))),
  ((row_pre) # Int  |-> (1 - 0 ))
  **  ((col_pre) # Int  |-> (1 - 0 ))
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (Zlength (moves))) ”
  &&  “ ((-0) <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ ((-0) <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ ((-0) <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ ((-0) <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 = 0) ”
  &&  “ (0 = 0) ”
  &&  “ (PrefixWindow moves 0 0 0 0 0 0 0 ) ”
  &&  “ (WindowFits n_pre m_pre 0 0 0 0 ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (PreH1 : ((1 - 0 ) <= INT_MAX)) (PreH2 : ((1 - 0 ) >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85)))),
  ((row_pre) # Int  |-> (1 - 0 ))
  **  ((col_pre) # Int  |-> (1 - 0 ))
|--
  “ (WindowFits n_pre m_pre 0 0 0 0 ) ”
  &&  “ (PrefixWindow moves 0 0 0 0 0 0 0 ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (PreH1 : ((1 - 0 ) <= INT_MAX)) (PreH2 : ((1 - 0 ) >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85)))),
  ((row_pre) # Int  |-> (1 - 0 ))
  **  ((col_pre) # Int  |-> (1 - 0 ))
|--
  “ (WindowFits n_pre m_pre 0 0 0 0 ) ”
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (PreH1 : ((1 - 0 ) <= INT_MAX)) (PreH2 : ((1 - 0 ) >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85)))),
  ((row_pre) # Int  |-> (1 - 0 ))
  **  ((col_pre) # Int  |-> (1 - 0 ))
|--
  “ (PrefixWindow moves 0 0 0 0 0 0 0 ) ”
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (PreH1 : ((1 - 0 ) <= INT_MAX)) (PreH2 : ((1 - 0 ) >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85)))),
  ((row_pre) # Int  |-> (1 - 0 ))
  **  ((col_pre) # Int  |-> (1 - 0 ))
|--
  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
.

Definition solver_entail_wit_1_split_goal_spatial :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (PreH1 : ((1 - 0 ) <= INT_MAX)) (PreH2 : ((1 - 0 ) >= INT_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85)))),
  ((row_pre) # Int  |-> (1 - 0 ))
  **  ((col_pre) # Int  |-> (1 - 0 ))
|--
  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
.

Definition solver_entail_wit_2_1 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= (r - 1 )) ”
  &&  “ ((r - 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= (r - 1 )) ”
  &&  “ ((r - 1 ) <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) (r - 1 ) c (r - 1 ) maxr c maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) (r - 1 ) c (r - 1 ) maxr c maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) (r - 1 ) c (r - 1 ) maxr c maxc )
.

Definition solver_entail_wit_2_1_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_2 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= (r - 1 )) ”
  &&  “ ((r - 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= (r - 1 )) ”
  &&  “ ((r - 1 ) <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) (r - 1 ) c (r - 1 ) maxr minc c ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) (r - 1 ) c (r - 1 ) maxr minc c ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) (r - 1 ) c (r - 1 ) maxr minc c )
.

Definition solver_entail_wit_2_2_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_3 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= (r - 1 )) ”
  &&  “ ((r - 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= (r - 1 )) ”
  &&  “ ((r - 1 ) <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) (r - 1 ) c (r - 1 ) maxr minc maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) (r - 1 ) c (r - 1 ) maxr minc maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_3_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) (r - 1 ) c (r - 1 ) maxr minc maxc )
.

Definition solver_entail_wit_2_3_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_4 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1 ) > maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= (r - 1 )) ”
  &&  “ ((r - 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= (r - 1 )) ”
  &&  “ ((r - 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) (r - 1 ) c minr (r - 1 ) c maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1 ) > maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) (r - 1 ) c minr (r - 1 ) c maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_4_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1 ) > maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) (r - 1 ) c minr (r - 1 ) c maxc )
.

Definition solver_entail_wit_2_4_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1 ) > maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_5 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) > maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= (r - 1 )) ”
  &&  “ ((r - 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= (r - 1 )) ”
  &&  “ ((r - 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) (r - 1 ) c minr (r - 1 ) minc c ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) > maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) (r - 1 ) c minr (r - 1 ) minc c ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_5_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) > maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) (r - 1 ) c minr (r - 1 ) minc c )
.

Definition solver_entail_wit_2_5_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) > maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_6 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) > maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= (r - 1 )) ”
  &&  “ ((r - 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= (r - 1 )) ”
  &&  “ ((r - 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) (r - 1 ) c minr (r - 1 ) minc maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) > maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) (r - 1 ) c minr (r - 1 ) minc maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_6_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) > maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) (r - 1 ) c minr (r - 1 ) minc maxc )
.

Definition solver_entail_wit_2_6_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) > maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_7 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= (r - 1 )) ”
  &&  “ ((r - 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) (r - 1 ) c minr maxr c maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) (r - 1 ) c minr maxr c maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_7_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) (r - 1 ) c minr maxr c maxc )
.

Definition solver_entail_wit_2_7_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_8 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= (r - 1 )) ”
  &&  “ ((r - 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) (r - 1 ) c minr maxr minc c ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) (r - 1 ) c minr maxr minc c ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_8_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) (r - 1 ) c minr maxr minc c )
.

Definition solver_entail_wit_2_8_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_9 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= (r - 1 )) ”
  &&  “ ((r - 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) (r - 1 ) c minr maxr minc maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) (r - 1 ) c minr maxr minc maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_9_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) (r - 1 ) c minr maxr minc maxc )
.

Definition solver_entail_wit_2_9_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r - 1 ) <= maxr)) (PreH4 : ((r - 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_10 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) (r + 1 ) c (r + 1 ) maxr c maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) (r + 1 ) c (r + 1 ) maxr c maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_10_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) (r + 1 ) c (r + 1 ) maxr c maxc )
.

Definition solver_entail_wit_2_10_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_11 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) (r + 1 ) c (r + 1 ) maxr minc c ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) (r + 1 ) c (r + 1 ) maxr minc c ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_11_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) (r + 1 ) c (r + 1 ) maxr minc c )
.

Definition solver_entail_wit_2_11_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_12 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) (r + 1 ) c (r + 1 ) maxr minc maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) (r + 1 ) c (r + 1 ) maxr minc maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_12_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) (r + 1 ) c (r + 1 ) maxr minc maxc )
.

Definition solver_entail_wit_2_12_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_13 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1 ) > maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) (r + 1 ) c minr (r + 1 ) c maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1 ) > maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) (r + 1 ) c minr (r + 1 ) c maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_13_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1 ) > maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) (r + 1 ) c minr (r + 1 ) c maxc )
.

Definition solver_entail_wit_2_13_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1 ) > maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_14 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) > maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) (r + 1 ) c minr (r + 1 ) minc c ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) > maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) (r + 1 ) c minr (r + 1 ) minc c ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_14_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) > maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) (r + 1 ) c minr (r + 1 ) minc c )
.

Definition solver_entail_wit_2_14_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) > maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_15 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) > maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) (r + 1 ) c minr (r + 1 ) minc maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) > maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) (r + 1 ) c minr (r + 1 ) minc maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_15_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) > maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) (r + 1 ) c minr (r + 1 ) minc maxc )
.

Definition solver_entail_wit_2_15_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) > maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_16 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) (r + 1 ) c minr maxr c maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) (r + 1 ) c minr maxr c maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_16_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) (r + 1 ) c minr maxr c maxc )
.

Definition solver_entail_wit_2_16_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c < minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_17 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) (r + 1 ) c minr maxr minc c ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) (r + 1 ) c minr maxr minc c ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_17_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) (r + 1 ) c minr maxr minc c )
.

Definition solver_entail_wit_2_17_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c > maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_18 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) (r + 1 ) c minr maxr minc maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) (r + 1 ) c minr maxr minc maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_18_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) (r + 1 ) c minr maxr minc maxc )
.

Definition solver_entail_wit_2_18_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (c <= maxc)) (PreH2 : (c >= minc)) (PreH3 : ((r + 1 ) <= maxr)) (PreH4 : ((r + 1 ) >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_19 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c - 1 )) ”
  &&  “ ((c - 1 ) <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c - 1 )) ”
  &&  “ ((c - 1 ) <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) r (c - 1 ) r maxr (c - 1 ) maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) r (c - 1 ) r maxr (c - 1 ) maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_19_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) r (c - 1 ) r maxr (c - 1 ) maxc )
.

Definition solver_entail_wit_2_19_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_20 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) > maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c - 1 )) ”
  &&  “ ((c - 1 ) <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= (c - 1 )) ”
  &&  “ ((c - 1 ) <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) r (c - 1 ) r maxr minc (c - 1 ) ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) > maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) r (c - 1 ) r maxr minc (c - 1 ) ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_20_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) > maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) r (c - 1 ) r maxr minc (c - 1 ) )
.

Definition solver_entail_wit_2_20_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) > maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_21 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c - 1 )) ”
  &&  “ ((c - 1 ) <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) r (c - 1 ) r maxr minc maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) r (c - 1 ) r maxr minc maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_21_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) r (c - 1 ) r maxr minc maxc )
.

Definition solver_entail_wit_2_21_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_22 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) < minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c - 1 )) ”
  &&  “ ((c - 1 ) <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c - 1 )) ”
  &&  “ ((c - 1 ) <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) r (c - 1 ) minr r (c - 1 ) maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) < minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) r (c - 1 ) minr r (c - 1 ) maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_22_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) < minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) r (c - 1 ) minr r (c - 1 ) maxc )
.

Definition solver_entail_wit_2_22_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) < minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_23 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) > maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c - 1 )) ”
  &&  “ ((c - 1 ) <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= (c - 1 )) ”
  &&  “ ((c - 1 ) <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) r (c - 1 ) minr r minc (c - 1 ) ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) > maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) r (c - 1 ) minr r minc (c - 1 ) ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_23_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) > maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) r (c - 1 ) minr r minc (c - 1 ) )
.

Definition solver_entail_wit_2_23_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) > maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_24 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c - 1 )) ”
  &&  “ ((c - 1 ) <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) r (c - 1 ) minr r minc maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) r (c - 1 ) minr r minc maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_24_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) r (c - 1 ) minr r minc maxc )
.

Definition solver_entail_wit_2_24_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_25 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c - 1 )) ”
  &&  “ ((c - 1 ) <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c - 1 )) ”
  &&  “ ((c - 1 ) <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) r (c - 1 ) minr maxr (c - 1 ) maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) r (c - 1 ) minr maxr (c - 1 ) maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_25_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) r (c - 1 ) minr maxr (c - 1 ) maxc )
.

Definition solver_entail_wit_2_25_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_26 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) > maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c - 1 )) ”
  &&  “ ((c - 1 ) <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= (c - 1 )) ”
  &&  “ ((c - 1 ) <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) r (c - 1 ) minr maxr minc (c - 1 ) ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) > maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) r (c - 1 ) minr maxr minc (c - 1 ) ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_26_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) > maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) r (c - 1 ) minr maxr minc (c - 1 ) )
.

Definition solver_entail_wit_2_26_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) > maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_27 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c - 1 )) ”
  &&  “ ((c - 1 ) <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) r (c - 1 ) minr maxr minc maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) r (c - 1 ) minr maxr minc maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_27_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) r (c - 1 ) minr maxr minc maxc )
.

Definition solver_entail_wit_2_27_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c - 1 ) <= maxc)) (PreH2 : ((c - 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 = (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_28 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) r (c + 1 ) r maxr (c + 1 ) maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) r (c + 1 ) r maxr (c + 1 ) maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_28_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) r (c + 1 ) r maxr (c + 1 ) maxc )
.

Definition solver_entail_wit_2_28_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_29 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) > maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) r (c + 1 ) r maxr minc (c + 1 ) ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) > maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) r (c + 1 ) r maxr minc (c + 1 ) ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_29_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) > maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) r (c + 1 ) r maxr minc (c + 1 ) )
.

Definition solver_entail_wit_2_29_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) > maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_30 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) r (c + 1 ) r maxr minc maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) r (c + 1 ) r maxr minc maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_30_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) r (c + 1 ) r maxr minc maxc )
.

Definition solver_entail_wit_2_30_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r < minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_31 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) < minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) r (c + 1 ) minr r (c + 1 ) maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) < minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) r (c + 1 ) minr r (c + 1 ) maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_31_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) < minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) r (c + 1 ) minr r (c + 1 ) maxc )
.

Definition solver_entail_wit_2_31_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) < minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_32 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) > maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) r (c + 1 ) minr r minc (c + 1 ) ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) > maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) r (c + 1 ) minr r minc (c + 1 ) ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_32_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) > maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) r (c + 1 ) minr r minc (c + 1 ) )
.

Definition solver_entail_wit_2_32_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) > maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_33 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) r (c + 1 ) minr r minc maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) r (c + 1 ) minr r minc maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_33_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) r (c + 1 ) minr r minc maxc )
.

Definition solver_entail_wit_2_33_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r > maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_34 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) r (c + 1 ) minr maxr (c + 1 ) maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) r (c + 1 ) minr maxr (c + 1 ) maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_34_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) r (c + 1 ) minr maxr (c + 1 ) maxc )
.

Definition solver_entail_wit_2_34_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) < minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_35 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) > maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) r (c + 1 ) minr maxr minc (c + 1 ) ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) > maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) r (c + 1 ) minr maxr minc (c + 1 ) ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_35_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) > maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) r (c + 1 ) minr maxr minc (c + 1 ) )
.

Definition solver_entail_wit_2_35_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) > maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_2_36 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  EX (oldr: Z) (oldc: Z),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= (c + 1 )) ”
  &&  “ ((c + 1 ) <= (i + 1 )) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ ((-(i + 1 )) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i oldr oldc minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ (PrefixWindow moves (i + 1 ) r (c + 1 ) minr maxr minc maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  TT && emp 
|--
  “ (PrefixWindow moves (i + 1 ) r (c + 1 ) minr maxr minc maxc ) ”
  &&  “ (i < (Zlength (moves))) ”
  &&  emp
).

Definition solver_entail_wit_2_36_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (PrefixWindow moves (i + 1 ) r (c + 1 ) minr maxr minc maxc )
.

Definition solver_entail_wit_2_36_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : ((c + 1 ) <= maxc)) (PreH2 : ((c + 1 ) >= minc)) (PreH3 : (r <= maxr)) (PreH4 : (r >= minr)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (moves)))) (PreH14 : ((-i) <= r)) (PreH15 : (r <= i)) (PreH16 : ((-i) <= c)) (PreH17 : (c <= i)) (PreH18 : ((-i) <= minr)) (PreH19 : (minr <= 0)) (PreH20 : (0 <= maxr)) (PreH21 : (maxr <= i)) (PreH22 : ((-i) <= minc)) (PreH23 : (minc <= 0)) (PreH24 : (0 <= maxc)) (PreH25 : (maxc <= i)) (PreH26 : (br = 0)) (PreH27 : (bc = 0)) (PreH28 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH29 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH30 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH31 : (85 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH32 : (68 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))) (PreH33 : (76 <> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))),
  (i < (Zlength (moves)))
.

Definition solver_entail_wit_3 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (oldr: Z) (oldc: Z) (i: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (nminr: Z) (nmaxr: Z) (nminc: Z) (nmaxc: Z) (br: Z) (bc: Z) (PreH1 : ((nmaxc - nminc ) < m_pre)) (PreH2 : ((nmaxr - nminr ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength (moves)))) (PreH12 : ((-(i + 1 )) <= r)) (PreH13 : (r <= (i + 1 ))) (PreH14 : ((-(i + 1 )) <= c)) (PreH15 : (c <= (i + 1 ))) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= 0)) (PreH18 : (0 <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= 0)) (PreH22 : (0 <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : ((-(i + 1 )) <= nminr)) (PreH25 : (nminr <= 0)) (PreH26 : (0 <= nmaxr)) (PreH27 : (nmaxr <= (i + 1 ))) (PreH28 : ((-(i + 1 )) <= nminc)) (PreH29 : (nminc <= 0)) (PreH30 : (0 <= nmaxc)) (PreH31 : (nmaxc <= (i + 1 ))) (PreH32 : (br = 0)) (PreH33 : (bc = 0)) (PreH34 : (PrefixWindow moves i oldr oldc minr maxr minc maxc )) (PreH35 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH36 : (PrefixWindow moves (i + 1 ) r c nminr nmaxr nminc nmaxc )),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (moves))) ”
  &&  “ ((-(i + 1 )) <= r) ”
  &&  “ (r <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= c) ”
  &&  “ (c <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= nminr) ”
  &&  “ (nminr <= 0) ”
  &&  “ (0 <= nmaxr) ”
  &&  “ (nmaxr <= (i + 1 )) ”
  &&  “ ((-(i + 1 )) <= nminc) ”
  &&  “ (nminc <= 0) ”
  &&  “ (0 <= nmaxc) ”
  &&  “ (nmaxc <= (i + 1 )) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves (i + 1 ) r c nminr nmaxr nminc nmaxc ) ”
  &&  “ (WindowFits n_pre m_pre nminr nmaxr nminc nmaxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (oldr: Z) (oldc: Z) (i: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (nminr: Z) (nmaxr: Z) (nminc: Z) (nmaxc: Z) (br: Z) (bc: Z) (PreH1 : ((nmaxc - nminc ) < m_pre)) (PreH2 : ((nmaxr - nminr ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength (moves)))) (PreH12 : ((-(i + 1 )) <= r)) (PreH13 : (r <= (i + 1 ))) (PreH14 : ((-(i + 1 )) <= c)) (PreH15 : (c <= (i + 1 ))) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= 0)) (PreH18 : (0 <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= 0)) (PreH22 : (0 <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : ((-(i + 1 )) <= nminr)) (PreH25 : (nminr <= 0)) (PreH26 : (0 <= nmaxr)) (PreH27 : (nmaxr <= (i + 1 ))) (PreH28 : ((-(i + 1 )) <= nminc)) (PreH29 : (nminc <= 0)) (PreH30 : (0 <= nmaxc)) (PreH31 : (nmaxc <= (i + 1 ))) (PreH32 : (br = 0)) (PreH33 : (bc = 0)) (PreH34 : (PrefixWindow moves i oldr oldc minr maxr minc maxc )) (PreH35 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH36 : (PrefixWindow moves (i + 1 ) r c nminr nmaxr nminc nmaxc )),
  TT && emp 
|--
  “ (WindowFits n_pre m_pre nminr nmaxr nminc nmaxc ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (oldr: Z) (oldc: Z) (i: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (nminr: Z) (nmaxr: Z) (nminc: Z) (nmaxc: Z) (br: Z) (bc: Z) (PreH1 : ((nmaxc - nminc ) < m_pre)) (PreH2 : ((nmaxr - nminr ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength (moves)))) (PreH12 : ((-(i + 1 )) <= r)) (PreH13 : (r <= (i + 1 ))) (PreH14 : ((-(i + 1 )) <= c)) (PreH15 : (c <= (i + 1 ))) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= 0)) (PreH18 : (0 <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= 0)) (PreH22 : (0 <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : ((-(i + 1 )) <= nminr)) (PreH25 : (nminr <= 0)) (PreH26 : (0 <= nmaxr)) (PreH27 : (nmaxr <= (i + 1 ))) (PreH28 : ((-(i + 1 )) <= nminc)) (PreH29 : (nminc <= 0)) (PreH30 : (0 <= nmaxc)) (PreH31 : (nmaxc <= (i + 1 ))) (PreH32 : (br = 0)) (PreH33 : (bc = 0)) (PreH34 : (PrefixWindow moves i oldr oldc minr maxr minc maxc )) (PreH35 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH36 : (PrefixWindow moves (i + 1 ) r c nminr nmaxr nminc nmaxc )),
  (WindowFits n_pre m_pre nminr nmaxr nminc nmaxc )
.

Definition solver_entail_wit_3_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (oldr: Z) (oldc: Z) (i: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (nminr: Z) (nmaxr: Z) (nminc: Z) (nmaxc: Z) (br: Z) (bc: Z) (PreH1 : ((nmaxc - nminc ) < m_pre)) (PreH2 : ((nmaxr - nminr ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength (moves)))) (PreH12 : ((-(i + 1 )) <= r)) (PreH13 : (r <= (i + 1 ))) (PreH14 : ((-(i + 1 )) <= c)) (PreH15 : (c <= (i + 1 ))) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= 0)) (PreH18 : (0 <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= 0)) (PreH22 : (0 <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : ((-(i + 1 )) <= nminr)) (PreH25 : (nminr <= 0)) (PreH26 : (0 <= nmaxr)) (PreH27 : (nmaxr <= (i + 1 ))) (PreH28 : ((-(i + 1 )) <= nminc)) (PreH29 : (nminc <= 0)) (PreH30 : (0 <= nmaxc)) (PreH31 : (nmaxc <= (i + 1 ))) (PreH32 : (br = 0)) (PreH33 : (bc = 0)) (PreH34 : (PrefixWindow moves i oldr oldc minr maxr minc maxc )) (PreH35 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH36 : (PrefixWindow moves (i + 1 ) r c nminr nmaxr nminc nmaxc )),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))
.

Definition solver_entail_wit_4_1 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= 0)) (PreH16 : (0 <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= 0)) (PreH20 : (0 <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = 0)) (PreH23 : (bc = 0)) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH26 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ ((-(Zlength (moves))) <= r) ”
  &&  “ (r <= (Zlength (moves))) ”
  &&  “ ((-(Zlength (moves))) <= c) ”
  &&  “ (c <= (Zlength (moves))) ”
  &&  “ ((-(Zlength (moves))) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (Zlength (moves))) ”
  &&  “ ((-(Zlength (moves))) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (Zlength (moves))) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= 0)) (PreH16 : (0 <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= 0)) (PreH20 : (0 <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = 0)) (PreH23 : (bc = 0)) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH26 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) = 0)),
  TT && emp 
|--
  “ (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  emp
).

Definition solver_entail_wit_4_1_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= 0)) (PreH16 : (0 <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= 0)) (PreH20 : (0 <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = 0)) (PreH23 : (bc = 0)) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH26 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) = 0)),
  (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc )
.

Definition solver_entail_wit_4_1_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= 0)) (PreH16 : (0 <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= 0)) (PreH20 : (0 <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = 0)) (PreH23 : (bc = 0)) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH26 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) = 0)),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))
.

Definition solver_entail_wit_4_2 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (oldr: Z) (oldc: Z) (i: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (nminr: Z) (nmaxr: Z) (nminc: Z) (nmaxc: Z) (br: Z) (bc: Z) (PreH1 : ((nmaxr - nminr ) >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000)) (PreH6 : (1 <= (Zlength (moves)))) (PreH7 : ((Zlength (moves)) <= 1000000)) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength (moves)))) (PreH11 : ((-(i + 1 )) <= r)) (PreH12 : (r <= (i + 1 ))) (PreH13 : ((-(i + 1 )) <= c)) (PreH14 : (c <= (i + 1 ))) (PreH15 : ((-i) <= minr)) (PreH16 : (minr <= 0)) (PreH17 : (0 <= maxr)) (PreH18 : (maxr <= i)) (PreH19 : ((-i) <= minc)) (PreH20 : (minc <= 0)) (PreH21 : (0 <= maxc)) (PreH22 : (maxc <= i)) (PreH23 : ((-(i + 1 )) <= nminr)) (PreH24 : (nminr <= 0)) (PreH25 : (0 <= nmaxr)) (PreH26 : (nmaxr <= (i + 1 ))) (PreH27 : ((-(i + 1 )) <= nminc)) (PreH28 : (nminc <= 0)) (PreH29 : (0 <= nmaxc)) (PreH30 : (nmaxc <= (i + 1 ))) (PreH31 : (br = 0)) (PreH32 : (bc = 0)) (PreH33 : (PrefixWindow moves i oldr oldc minr maxr minc maxc )) (PreH34 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH35 : (PrefixWindow moves (i + 1 ) r c nminr nmaxr nminc nmaxc )),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ ((-(Zlength (moves))) <= r) ”
  &&  “ (r <= (Zlength (moves))) ”
  &&  “ ((-(Zlength (moves))) <= c) ”
  &&  “ (c <= (Zlength (moves))) ”
  &&  “ ((-(Zlength (moves))) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (Zlength (moves))) ”
  &&  “ ((-(Zlength (moves))) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (Zlength (moves))) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (oldr: Z) (oldc: Z) (i: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (nminr: Z) (nmaxr: Z) (nminc: Z) (nmaxc: Z) (br: Z) (bc: Z) (PreH1 : ((nmaxr - nminr ) >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000)) (PreH6 : (1 <= (Zlength (moves)))) (PreH7 : ((Zlength (moves)) <= 1000000)) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength (moves)))) (PreH11 : ((-(i + 1 )) <= r)) (PreH12 : (r <= (i + 1 ))) (PreH13 : ((-(i + 1 )) <= c)) (PreH14 : (c <= (i + 1 ))) (PreH15 : ((-i) <= minr)) (PreH16 : (minr <= 0)) (PreH17 : (0 <= maxr)) (PreH18 : (maxr <= i)) (PreH19 : ((-i) <= minc)) (PreH20 : (minc <= 0)) (PreH21 : (0 <= maxc)) (PreH22 : (maxc <= i)) (PreH23 : ((-(i + 1 )) <= nminr)) (PreH24 : (nminr <= 0)) (PreH25 : (0 <= nmaxr)) (PreH26 : (nmaxr <= (i + 1 ))) (PreH27 : ((-(i + 1 )) <= nminc)) (PreH28 : (nminc <= 0)) (PreH29 : (0 <= nmaxc)) (PreH30 : (nmaxc <= (i + 1 ))) (PreH31 : (br = 0)) (PreH32 : (bc = 0)) (PreH33 : (PrefixWindow moves i oldr oldc minr maxr minc maxc )) (PreH34 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH35 : (PrefixWindow moves (i + 1 ) r c nminr nmaxr nminc nmaxc )),
  TT && emp 
|--
  “ (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  emp
).

Definition solver_entail_wit_4_2_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (oldr: Z) (oldc: Z) (i: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (nminr: Z) (nmaxr: Z) (nminc: Z) (nmaxc: Z) (br: Z) (bc: Z) (PreH1 : ((nmaxr - nminr ) >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000)) (PreH6 : (1 <= (Zlength (moves)))) (PreH7 : ((Zlength (moves)) <= 1000000)) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength (moves)))) (PreH11 : ((-(i + 1 )) <= r)) (PreH12 : (r <= (i + 1 ))) (PreH13 : ((-(i + 1 )) <= c)) (PreH14 : (c <= (i + 1 ))) (PreH15 : ((-i) <= minr)) (PreH16 : (minr <= 0)) (PreH17 : (0 <= maxr)) (PreH18 : (maxr <= i)) (PreH19 : ((-i) <= minc)) (PreH20 : (minc <= 0)) (PreH21 : (0 <= maxc)) (PreH22 : (maxc <= i)) (PreH23 : ((-(i + 1 )) <= nminr)) (PreH24 : (nminr <= 0)) (PreH25 : (0 <= nmaxr)) (PreH26 : (nmaxr <= (i + 1 ))) (PreH27 : ((-(i + 1 )) <= nminc)) (PreH28 : (nminc <= 0)) (PreH29 : (0 <= nmaxc)) (PreH30 : (nmaxc <= (i + 1 ))) (PreH31 : (br = 0)) (PreH32 : (bc = 0)) (PreH33 : (PrefixWindow moves i oldr oldc minr maxr minc maxc )) (PreH34 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH35 : (PrefixWindow moves (i + 1 ) r c nminr nmaxr nminc nmaxc )),
  (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc )
.

Definition solver_entail_wit_4_2_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (oldr: Z) (oldc: Z) (i: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (nminr: Z) (nmaxr: Z) (nminc: Z) (nmaxc: Z) (br: Z) (bc: Z) (PreH1 : ((nmaxr - nminr ) >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000)) (PreH6 : (1 <= (Zlength (moves)))) (PreH7 : ((Zlength (moves)) <= 1000000)) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH9 : (0 <= i)) (PreH10 : (i < (Zlength (moves)))) (PreH11 : ((-(i + 1 )) <= r)) (PreH12 : (r <= (i + 1 ))) (PreH13 : ((-(i + 1 )) <= c)) (PreH14 : (c <= (i + 1 ))) (PreH15 : ((-i) <= minr)) (PreH16 : (minr <= 0)) (PreH17 : (0 <= maxr)) (PreH18 : (maxr <= i)) (PreH19 : ((-i) <= minc)) (PreH20 : (minc <= 0)) (PreH21 : (0 <= maxc)) (PreH22 : (maxc <= i)) (PreH23 : ((-(i + 1 )) <= nminr)) (PreH24 : (nminr <= 0)) (PreH25 : (0 <= nmaxr)) (PreH26 : (nmaxr <= (i + 1 ))) (PreH27 : ((-(i + 1 )) <= nminc)) (PreH28 : (nminc <= 0)) (PreH29 : (0 <= nmaxc)) (PreH30 : (nmaxc <= (i + 1 ))) (PreH31 : (br = 0)) (PreH32 : (bc = 0)) (PreH33 : (PrefixWindow moves i oldr oldc minr maxr minc maxc )) (PreH34 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH35 : (PrefixWindow moves (i + 1 ) r c nminr nmaxr nminc nmaxc )),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))
.

Definition solver_entail_wit_4_3 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (oldr: Z) (oldc: Z) (i: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (nminr: Z) (nmaxr: Z) (nminc: Z) (nmaxc: Z) (br: Z) (bc: Z) (PreH1 : ((nmaxc - nminc ) >= m_pre)) (PreH2 : ((nmaxr - nminr ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength (moves)))) (PreH12 : ((-(i + 1 )) <= r)) (PreH13 : (r <= (i + 1 ))) (PreH14 : ((-(i + 1 )) <= c)) (PreH15 : (c <= (i + 1 ))) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= 0)) (PreH18 : (0 <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= 0)) (PreH22 : (0 <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : ((-(i + 1 )) <= nminr)) (PreH25 : (nminr <= 0)) (PreH26 : (0 <= nmaxr)) (PreH27 : (nmaxr <= (i + 1 ))) (PreH28 : ((-(i + 1 )) <= nminc)) (PreH29 : (nminc <= 0)) (PreH30 : (0 <= nmaxc)) (PreH31 : (nmaxc <= (i + 1 ))) (PreH32 : (br = 0)) (PreH33 : (bc = 0)) (PreH34 : (PrefixWindow moves i oldr oldc minr maxr minc maxc )) (PreH35 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH36 : (PrefixWindow moves (i + 1 ) r c nminr nmaxr nminc nmaxc )),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ ((-(Zlength (moves))) <= r) ”
  &&  “ (r <= (Zlength (moves))) ”
  &&  “ ((-(Zlength (moves))) <= c) ”
  &&  “ (c <= (Zlength (moves))) ”
  &&  “ ((-(Zlength (moves))) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (Zlength (moves))) ”
  &&  “ ((-(Zlength (moves))) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (Zlength (moves))) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (oldr: Z) (oldc: Z) (i: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (nminr: Z) (nmaxr: Z) (nminc: Z) (nmaxc: Z) (br: Z) (bc: Z) (PreH1 : ((nmaxc - nminc ) >= m_pre)) (PreH2 : ((nmaxr - nminr ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength (moves)))) (PreH12 : ((-(i + 1 )) <= r)) (PreH13 : (r <= (i + 1 ))) (PreH14 : ((-(i + 1 )) <= c)) (PreH15 : (c <= (i + 1 ))) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= 0)) (PreH18 : (0 <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= 0)) (PreH22 : (0 <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : ((-(i + 1 )) <= nminr)) (PreH25 : (nminr <= 0)) (PreH26 : (0 <= nmaxr)) (PreH27 : (nmaxr <= (i + 1 ))) (PreH28 : ((-(i + 1 )) <= nminc)) (PreH29 : (nminc <= 0)) (PreH30 : (0 <= nmaxc)) (PreH31 : (nmaxc <= (i + 1 ))) (PreH32 : (br = 0)) (PreH33 : (bc = 0)) (PreH34 : (PrefixWindow moves i oldr oldc minr maxr minc maxc )) (PreH35 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH36 : (PrefixWindow moves (i + 1 ) r c nminr nmaxr nminc nmaxc )),
  TT && emp 
|--
  “ (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  emp
).

Definition solver_entail_wit_4_3_split_goal_1 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (oldr: Z) (oldc: Z) (i: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (nminr: Z) (nmaxr: Z) (nminc: Z) (nmaxc: Z) (br: Z) (bc: Z) (PreH1 : ((nmaxc - nminc ) >= m_pre)) (PreH2 : ((nmaxr - nminr ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength (moves)))) (PreH12 : ((-(i + 1 )) <= r)) (PreH13 : (r <= (i + 1 ))) (PreH14 : ((-(i + 1 )) <= c)) (PreH15 : (c <= (i + 1 ))) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= 0)) (PreH18 : (0 <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= 0)) (PreH22 : (0 <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : ((-(i + 1 )) <= nminr)) (PreH25 : (nminr <= 0)) (PreH26 : (0 <= nmaxr)) (PreH27 : (nmaxr <= (i + 1 ))) (PreH28 : ((-(i + 1 )) <= nminc)) (PreH29 : (nminc <= 0)) (PreH30 : (0 <= nmaxc)) (PreH31 : (nmaxc <= (i + 1 ))) (PreH32 : (br = 0)) (PreH33 : (bc = 0)) (PreH34 : (PrefixWindow moves i oldr oldc minr maxr minc maxc )) (PreH35 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH36 : (PrefixWindow moves (i + 1 ) r c nminr nmaxr nminc nmaxc )),
  (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc )
.

Definition solver_entail_wit_4_3_split_goal_2 :=
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (oldr: Z) (oldc: Z) (i: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (nminr: Z) (nmaxr: Z) (nminc: Z) (nmaxc: Z) (br: Z) (bc: Z) (PreH1 : ((nmaxc - nminc ) >= m_pre)) (PreH2 : ((nmaxr - nminr ) < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 1000000)) (PreH7 : (1 <= (Zlength (moves)))) (PreH8 : ((Zlength (moves)) <= 1000000)) (PreH9 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (moves)))) -> (((((Znth k_2 moves 0) = 76) \/ ((Znth k_2 moves 0) = 82)) \/ ((Znth k_2 moves 0) = 68)) \/ ((Znth k_2 moves 0) = 85)))) (PreH10 : (0 <= i)) (PreH11 : (i < (Zlength (moves)))) (PreH12 : ((-(i + 1 )) <= r)) (PreH13 : (r <= (i + 1 ))) (PreH14 : ((-(i + 1 )) <= c)) (PreH15 : (c <= (i + 1 ))) (PreH16 : ((-i) <= minr)) (PreH17 : (minr <= 0)) (PreH18 : (0 <= maxr)) (PreH19 : (maxr <= i)) (PreH20 : ((-i) <= minc)) (PreH21 : (minc <= 0)) (PreH22 : (0 <= maxc)) (PreH23 : (maxc <= i)) (PreH24 : ((-(i + 1 )) <= nminr)) (PreH25 : (nminr <= 0)) (PreH26 : (0 <= nmaxr)) (PreH27 : (nmaxr <= (i + 1 ))) (PreH28 : ((-(i + 1 )) <= nminc)) (PreH29 : (nminc <= 0)) (PreH30 : (0 <= nmaxc)) (PreH31 : (nmaxc <= (i + 1 ))) (PreH32 : (br = 0)) (PreH33 : (bc = 0)) (PreH34 : (PrefixWindow moves i oldr oldc minr maxr minc maxc )) (PreH35 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH36 : (PrefixWindow moves (i + 1 ) r c nminr nmaxr nminc nmaxc )),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))
.

Definition solver_return_wit_1 :=
(
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (br: Z) (bc: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH8 : ((-(Zlength (moves))) <= r)) (PreH9 : (r <= (Zlength (moves)))) (PreH10 : ((-(Zlength (moves))) <= c)) (PreH11 : (c <= (Zlength (moves)))) (PreH12 : ((-(Zlength (moves))) <= minr)) (PreH13 : (minr <= 0)) (PreH14 : (0 <= maxr)) (PreH15 : (maxr <= (Zlength (moves)))) (PreH16 : ((-(Zlength (moves))) <= minc)) (PreH17 : (minc <= 0)) (PreH18 : (0 <= maxc)) (PreH19 : (maxc <= (Zlength (moves)))) (PreH20 : (br = 0)) (PreH21 : (bc = 0)) (PreH22 : (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc )),
  ((row_pre) # Int  |-> (1 - minr ))
  **  ((col_pre) # Int  |-> (1 - minc ))
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
|--
  EX (out: (Z * Z)),
  “ (Spec n_pre m_pre moves out ) ”
  &&  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons ((fst (out))) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons ((snd (out))) ((@nil Z))) )
) \/
(
forall (moves: (@list Z)) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (br: Z) (bc: Z) (PreH1 : ((1 - minc ) <= INT_MAX)) (PreH2 : ((1 - minr ) <= INT_MAX)) (PreH3 : ((1 - minc ) >= INT_MIN)) (PreH4 : ((1 - minr ) >= INT_MIN)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 1000000)) (PreH9 : (1 <= (Zlength (moves)))) (PreH10 : ((Zlength (moves)) <= 1000000)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH12 : ((-(Zlength (moves))) <= r)) (PreH13 : (r <= (Zlength (moves)))) (PreH14 : ((-(Zlength (moves))) <= c)) (PreH15 : (c <= (Zlength (moves)))) (PreH16 : ((-(Zlength (moves))) <= minr)) (PreH17 : (minr <= 0)) (PreH18 : (0 <= maxr)) (PreH19 : (maxr <= (Zlength (moves)))) (PreH20 : ((-(Zlength (moves))) <= minc)) (PreH21 : (minc <= 0)) (PreH22 : (0 <= maxc)) (PreH23 : (maxc <= (Zlength (moves)))) (PreH24 : (br = 0)) (PreH25 : (bc = 0)) (PreH26 : (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc )),
  ((row_pre) # Int  |-> (1 - minr ))
  **  ((col_pre) # Int  |-> (1 - minc ))
|--
  EX (out: (Z * Z)),
  “ (Spec n_pre m_pre moves out ) ”
  &&  (IntArray.full row_pre 1 (cons ((fst (out))) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons ((snd (out))) ((@nil Z))) )
).

Definition solver_partial_solve_wit_1 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85)))),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_full row_pre 1 )
  **  (IntArray.undef_full col_pre 1 )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (i: Z), (((0 <= i) /\ (i < (Zlength (moves)))) -> (((((Znth i moves 0) = 76) \/ ((Znth i moves 0) = 82)) \/ ((Znth i moves 0) = 68)) \/ ((Znth i moves 0) = 85))) ”
  &&  (IntArray.undef_full row_pre 1 )
  **  (IntArray.undef_full col_pre 1 )
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_2 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= 0)) (PreH16 : (0 <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= 0)) (PreH20 : (0 <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = 0)) (PreH23 : (bc = 0)) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc )),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (moves))) ”
  &&  “ ((-i) <= r) ”
  &&  “ (r <= i) ”
  &&  “ ((-i) <= c) ”
  &&  “ (c <= i) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i r c minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
.

Definition solver_partial_solve_wit_3 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (bc: Z) (br: Z) (maxc: Z) (minc: Z) (maxr: Z) (minr: Z) (c: Z) (r: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH8 : (0 <= i)) (PreH9 : (i <= (Zlength (moves)))) (PreH10 : ((-i) <= r)) (PreH11 : (r <= i)) (PreH12 : ((-i) <= c)) (PreH13 : (c <= i)) (PreH14 : ((-i) <= minr)) (PreH15 : (minr <= 0)) (PreH16 : (0 <= maxr)) (PreH17 : (maxr <= i)) (PreH18 : ((-i) <= minc)) (PreH19 : (minc <= 0)) (PreH20 : (0 <= maxc)) (PreH21 : (maxc <= i)) (PreH22 : (br = 0)) (PreH23 : (bc = 0)) (PreH24 : (PrefixWindow moves i r c minr maxr minc maxc )) (PreH25 : (WindowFits n_pre m_pre minr maxr minc maxc )) (PreH26 : ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (moves))) ”
  &&  “ ((-i) <= r) ”
  &&  “ (r <= i) ”
  &&  “ ((-i) <= c) ”
  &&  “ (c <= i) ”
  &&  “ ((-i) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= i) ”
  &&  “ ((-i) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= i) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (PrefixWindow moves i r c minr maxr minc maxc ) ”
  &&  “ (WindowFits n_pre m_pre minr maxr minc maxc ) ”
  &&  “ ((Znth i (app (moves) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (moves) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
.

Definition solver_partial_solve_wit_4 :=
forall (moves: (@list Z)) (s_pre: Z) (n_pre: Z) (m_pre: Z) (row_pre: Z) (col_pre: Z) (r: Z) (c: Z) (minr: Z) (maxr: Z) (minc: Z) (maxc: Z) (br: Z) (bc: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000)) (PreH5 : (1 <= (Zlength (moves)))) (PreH6 : ((Zlength (moves)) <= 1000000)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85)))) (PreH8 : ((-(Zlength (moves))) <= r)) (PreH9 : (r <= (Zlength (moves)))) (PreH10 : ((-(Zlength (moves))) <= c)) (PreH11 : (c <= (Zlength (moves)))) (PreH12 : ((-(Zlength (moves))) <= minr)) (PreH13 : (minr <= 0)) (PreH14 : (0 <= maxr)) (PreH15 : (maxr <= (Zlength (moves)))) (PreH16 : ((-(Zlength (moves))) <= minc)) (PreH17 : (minc <= 0)) (PreH18 : (0 <= maxc)) (PreH19 : (maxc <= (Zlength (moves)))) (PreH20 : (br = 0)) (PreH21 : (bc = 0)) (PreH22 : (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc )),
  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (1 <= (Zlength (moves))) ”
  &&  “ ((Zlength (moves)) <= 1000000) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (moves)))) -> (((((Znth k moves 0) = 76) \/ ((Znth k moves 0) = 82)) \/ ((Znth k moves 0) = 68)) \/ ((Znth k moves 0) = 85))) ”
  &&  “ ((-(Zlength (moves))) <= r) ”
  &&  “ (r <= (Zlength (moves))) ”
  &&  “ ((-(Zlength (moves))) <= c) ”
  &&  “ (c <= (Zlength (moves))) ”
  &&  “ ((-(Zlength (moves))) <= minr) ”
  &&  “ (minr <= 0) ”
  &&  “ (0 <= maxr) ”
  &&  “ (maxr <= (Zlength (moves))) ”
  &&  “ ((-(Zlength (moves))) <= minc) ”
  &&  “ (minc <= 0) ”
  &&  “ (0 <= maxc) ”
  &&  “ (maxc <= (Zlength (moves))) ”
  &&  “ (br = 0) ”
  &&  “ (bc = 0) ”
  &&  “ (OptimalPrefixWindow n_pre m_pre moves minr maxr minc maxc ) ”
  &&  (IntArray.full row_pre 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col_pre 1 (cons (1) ((@nil Z))) )
  **  (CharArray.full s_pre ((Zlength (moves)) + 1 ) (app (moves) ((cons (0) ((@nil Z))))) )
.

Definition solver_which_implies_wit_1 :=
(
forall (row: Z) (col: Z),
  (IntArray.undef_full row 1 )
  **  (IntArray.undef_full col 1 )
|--
  ((row) # Int  |->_)
  **  ((col) # Int  |->_)
) \/
(
forall (row: Z) (col: Z),
  (IntArray.undef_full row 1 )
  **  (IntArray.undef_full col 1 )
|--
  EX (x_2: Z) (x: Z),
  ((col) # Int  |-> x_2)
  **  ((row) # Int  |-> x)
).

Definition solver_which_implies_wit_2 :=
(
forall (row: Z) (col: Z),
  (IntArray.full row 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col 1 (cons (1) ((@nil Z))) )
|--
  ((row) # Int  |-> 1)
  **  ((col) # Int  |-> 1)
) \/
(
forall (row: Z) (col: Z),
  (IntArray.full row 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col 1 (cons (1) ((@nil Z))) )
|--
  ((row) # Int  |-> 1)
  **  ((col) # Int  |-> 1)
).

Definition solver_which_implies_wit_2_split_goal_spatial :=
forall (row: Z) (col: Z),
  (IntArray.full row 1 (cons (1) ((@nil Z))) )
  **  (IntArray.full col 1 (cons (1) ((@nil Z))) )
|--
  ((row) # Int  |-> 1)
  **  ((col) # Int  |-> 1)
.

Module Type VC_Correct.


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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Axiom proof_of_solver_entail_wit_2_4 : solver_entail_wit_2_4.
Axiom proof_of_solver_entail_wit_2_5 : solver_entail_wit_2_5.
Axiom proof_of_solver_entail_wit_2_6 : solver_entail_wit_2_6.
Axiom proof_of_solver_entail_wit_2_7 : solver_entail_wit_2_7.
Axiom proof_of_solver_entail_wit_2_8 : solver_entail_wit_2_8.
Axiom proof_of_solver_entail_wit_2_9 : solver_entail_wit_2_9.
Axiom proof_of_solver_entail_wit_2_10 : solver_entail_wit_2_10.
Axiom proof_of_solver_entail_wit_2_11 : solver_entail_wit_2_11.
Axiom proof_of_solver_entail_wit_2_12 : solver_entail_wit_2_12.
Axiom proof_of_solver_entail_wit_2_13 : solver_entail_wit_2_13.
Axiom proof_of_solver_entail_wit_2_14 : solver_entail_wit_2_14.
Axiom proof_of_solver_entail_wit_2_15 : solver_entail_wit_2_15.
Axiom proof_of_solver_entail_wit_2_16 : solver_entail_wit_2_16.
Axiom proof_of_solver_entail_wit_2_17 : solver_entail_wit_2_17.
Axiom proof_of_solver_entail_wit_2_18 : solver_entail_wit_2_18.
Axiom proof_of_solver_entail_wit_2_19 : solver_entail_wit_2_19.
Axiom proof_of_solver_entail_wit_2_20 : solver_entail_wit_2_20.
Axiom proof_of_solver_entail_wit_2_21 : solver_entail_wit_2_21.
Axiom proof_of_solver_entail_wit_2_22 : solver_entail_wit_2_22.
Axiom proof_of_solver_entail_wit_2_23 : solver_entail_wit_2_23.
Axiom proof_of_solver_entail_wit_2_24 : solver_entail_wit_2_24.
Axiom proof_of_solver_entail_wit_2_25 : solver_entail_wit_2_25.
Axiom proof_of_solver_entail_wit_2_26 : solver_entail_wit_2_26.
Axiom proof_of_solver_entail_wit_2_27 : solver_entail_wit_2_27.
Axiom proof_of_solver_entail_wit_2_28 : solver_entail_wit_2_28.
Axiom proof_of_solver_entail_wit_2_29 : solver_entail_wit_2_29.
Axiom proof_of_solver_entail_wit_2_30 : solver_entail_wit_2_30.
Axiom proof_of_solver_entail_wit_2_31 : solver_entail_wit_2_31.
Axiom proof_of_solver_entail_wit_2_32 : solver_entail_wit_2_32.
Axiom proof_of_solver_entail_wit_2_33 : solver_entail_wit_2_33.
Axiom proof_of_solver_entail_wit_2_34 : solver_entail_wit_2_34.
Axiom proof_of_solver_entail_wit_2_35 : solver_entail_wit_2_35.
Axiom proof_of_solver_entail_wit_2_36 : solver_entail_wit_2_36.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.
Axiom proof_of_solver_which_implies_wit_2 : solver_which_implies_wit_2.

End VC_Correct.
