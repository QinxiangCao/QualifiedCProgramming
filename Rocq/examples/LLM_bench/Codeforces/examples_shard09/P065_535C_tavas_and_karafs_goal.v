From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P065_535C_tavas_and_karafs_lib.
Local Open Scope sac.

(*----- Function height -----*)

Definition height_safety_wit_1 :=
forall (A_pre: Z) (B_pre: Z) (i_pre: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= i_pre)) (PreH6 : (i_pre <= 2000000)),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "i" ) )) # Int64  |-> i_pre)
|--
  “ ((A_pre + ((i_pre - 1 ) * B_pre ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (A_pre + ((i_pre - 1 ) * B_pre ) )) ”
.

Definition height_safety_wit_2 :=
forall (A_pre: Z) (B_pre: Z) (i_pre: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= i_pre)) (PreH6 : (i_pre <= 2000000)),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "i" ) )) # Int64  |-> i_pre)
|--
  “ (((i_pre - 1 ) * B_pre ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((i_pre - 1 ) * B_pre )) ”
.

Definition height_safety_wit_3 :=
forall (A_pre: Z) (B_pre: Z) (i_pre: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= i_pre)) (PreH6 : (i_pre <= 2000000)),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "i" ) )) # Int64  |-> i_pre)
|--
  “ ((i_pre - 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (i_pre - 1 )) ”
.

Definition height_safety_wit_4 :=
forall (A_pre: Z) (B_pre: Z) (i_pre: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= i_pre)) (PreH6 : (i_pre <= 2000000)),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "i" ) )) # Int64  |-> i_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition height_return_wit_1 :=
forall (A_pre: Z) (B_pre: Z) (i_pre: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= i_pre)) (PreH6 : (i_pre <= 2000000)),
  TT && emp 
|--
  “ ((A_pre + ((i_pre - 1 ) * B_pre ) ) = (A_pre + ((i_pre - 1 ) * B_pre ) )) ”
  &&  emp
.

(*----- Function range_sum -----*)

Definition range_sum_safety_wit_1 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (r_pre: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= r_pre)) (PreH7 : (r_pre <= 2000000)),
  ((( &( "cnt" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
|--
  “ (((r_pre - l_pre ) + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((r_pre - l_pre ) + 1 )) ”
.

Definition range_sum_safety_wit_2 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (r_pre: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= r_pre)) (PreH7 : (r_pre <= 2000000)),
  ((( &( "cnt" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
|--
  “ ((r_pre - l_pre ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (r_pre - l_pre )) ”
.

Definition range_sum_safety_wit_3 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (r_pre: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= r_pre)) (PreH7 : (r_pre <= 2000000)),
  ((( &( "cnt" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition range_sum_safety_wit_4 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (r_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (A_pre + ((r_pre - 1 ) * B_pre ) ))) (PreH2 : (retval = (A_pre + ((l_pre - 1 ) * B_pre ) ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= 1000000)) (PreH5 : (1 <= B_pre)) (PreH6 : (B_pre <= 1000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= r_pre)) (PreH9 : (r_pre <= 2000000)),
  ((( &( "cnt" ) )) # Int64  |-> ((r_pre - l_pre ) + 1 ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
|--
  “ ((((retval + retval_2 ) * ((r_pre - l_pre ) + 1 ) ) <> (INT64_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition range_sum_safety_wit_5 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (r_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (A_pre + ((r_pre - 1 ) * B_pre ) ))) (PreH2 : (retval = (A_pre + ((l_pre - 1 ) * B_pre ) ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= 1000000)) (PreH5 : (1 <= B_pre)) (PreH6 : (B_pre <= 1000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= r_pre)) (PreH9 : (r_pre <= 2000000)),
  ((( &( "cnt" ) )) # Int64  |-> ((r_pre - l_pre ) + 1 ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
|--
  “ (((retval + retval_2 ) * ((r_pre - l_pre ) + 1 ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((retval + retval_2 ) * ((r_pre - l_pre ) + 1 ) )) ”
.

Definition range_sum_safety_wit_6 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (r_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (A_pre + ((r_pre - 1 ) * B_pre ) ))) (PreH2 : (retval = (A_pre + ((l_pre - 1 ) * B_pre ) ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= 1000000)) (PreH5 : (1 <= B_pre)) (PreH6 : (B_pre <= 1000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= r_pre)) (PreH9 : (r_pre <= 2000000)),
  ((( &( "cnt" ) )) # Int64  |-> ((r_pre - l_pre ) + 1 ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (retval + retval_2 )) ”
.

Definition range_sum_safety_wit_7 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (r_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (A_pre + ((r_pre - 1 ) * B_pre ) ))) (PreH2 : (retval = (A_pre + ((l_pre - 1 ) * B_pre ) ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= 1000000)) (PreH5 : (1 <= B_pre)) (PreH6 : (B_pre <= 1000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= r_pre)) (PreH9 : (r_pre <= 2000000)),
  ((( &( "cnt" ) )) # Int64  |-> ((r_pre - l_pre ) + 1 ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition range_sum_return_wit_1 :=
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (r_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (A_pre + ((r_pre - 1 ) * B_pre ) ))) (PreH2 : (retval = (A_pre + ((l_pre - 1 ) * B_pre ) ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= 1000000)) (PreH5 : (1 <= B_pre)) (PreH6 : (B_pre <= 1000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= r_pre)) (PreH9 : (r_pre <= 2000000)),
  TT && emp 
|--
  “ ((((retval + retval_2 ) * ((r_pre - l_pre ) + 1 ) ) ÷ 2 ) = (((((A_pre + ((l_pre - 1 ) * B_pre ) ) + A_pre ) + ((r_pre - 1 ) * B_pre ) ) * ((r_pre - l_pre ) + 1 ) ) ÷ 2 )) ”
  &&  emp
) \/
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (r_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (A_pre + ((r_pre - 1 ) * B_pre ) ))) (PreH2 : (retval = (A_pre + ((l_pre - 1 ) * B_pre ) ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= 1000000)) (PreH5 : (1 <= B_pre)) (PreH6 : (B_pre <= 1000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= r_pre)) (PreH9 : (r_pre <= 2000000)),
  TT && emp 
|--
  “ (((((A_pre + ((l_pre - 1 ) * B_pre ) ) + (A_pre + ((r_pre - 1 ) * B_pre ) ) ) * ((r_pre - l_pre ) + 1 ) ) ÷ 2 ) = (((((A_pre + ((l_pre - 1 ) * B_pre ) ) + A_pre ) + ((r_pre - 1 ) * B_pre ) ) * ((r_pre - l_pre ) + 1 ) ) ÷ 2 )) ”
  &&  emp
).

Definition range_sum_return_wit_1_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (r_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (A_pre + ((r_pre - 1 ) * B_pre ) ))) (PreH2 : (retval = (A_pre + ((l_pre - 1 ) * B_pre ) ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= 1000000)) (PreH5 : (1 <= B_pre)) (PreH6 : (B_pre <= 1000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= r_pre)) (PreH9 : (r_pre <= 2000000)),
  (((((A_pre + ((l_pre - 1 ) * B_pre ) ) + (A_pre + ((r_pre - 1 ) * B_pre ) ) ) * ((r_pre - l_pre ) + 1 ) ) ÷ 2 ) = (((((A_pre + ((l_pre - 1 ) * B_pre ) ) + A_pre ) + ((r_pre - 1 ) * B_pre ) ) * ((r_pre - l_pre ) + 1 ) ) ÷ 2 ))
.

Definition range_sum_partial_solve_wit_1_pure :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (r_pre: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= r_pre)) (PreH7 : (r_pre <= 2000000)),
  ((( &( "cnt" ) )) # Int64  |-> ((r_pre - l_pre ) + 1 ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= l_pre) ”
  &&  “ (l_pre <= 2000000) ”
.

Definition range_sum_partial_solve_wit_1_aux :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (r_pre: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= r_pre)) (PreH7 : (r_pre <= 2000000)),
  TT && emp 
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= l_pre) ”
  &&  “ (l_pre <= 2000000) ”
  &&  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= l_pre) ”
  &&  “ (l_pre <= r_pre) ”
  &&  “ (r_pre <= 2000000) ”
  &&  emp
.

Definition range_sum_partial_solve_wit_1 := range_sum_partial_solve_wit_1_pure -> range_sum_partial_solve_wit_1_aux.

Definition range_sum_partial_solve_wit_2_pure :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (r_pre: Z) (retval: Z) (PreH1 : (retval = (A_pre + ((l_pre - 1 ) * B_pre ) ))) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= l_pre)) (PreH7 : (l_pre <= r_pre)) (PreH8 : (r_pre <= 2000000)),
  ((( &( "cnt" ) )) # Int64  |-> ((r_pre - l_pre ) + 1 ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= r_pre) ”
  &&  “ (r_pre <= 2000000) ”
.

Definition range_sum_partial_solve_wit_2_aux :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (r_pre: Z) (retval: Z) (PreH1 : (retval = (A_pre + ((l_pre - 1 ) * B_pre ) ))) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= l_pre)) (PreH7 : (l_pre <= r_pre)) (PreH8 : (r_pre <= 2000000)),
  TT && emp 
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= r_pre) ”
  &&  “ (r_pre <= 2000000) ”
  &&  “ (retval = (A_pre + ((l_pre - 1 ) * B_pre ) )) ”
  &&  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= l_pre) ”
  &&  “ (l_pre <= r_pre) ”
  &&  “ (r_pre <= 2000000) ”
  &&  emp
.

Definition range_sum_partial_solve_wit_2 := range_sum_partial_solve_wit_2_pure -> range_sum_partial_solve_wit_2_aux.

(*----- Function answer_query -----*)

Definition answer_query_safety_wit_1 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (retval: Z) (PreH1 : (retval > t_pre)) (PreH2 : (retval = (A_pre + ((l_pre - 1 ) * B_pre ) ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= 1000000)) (PreH5 : (1 <= B_pre)) (PreH6 : (B_pre <= 1000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= 1000000)) (PreH9 : (1 <= t_pre)) (PreH10 : (t_pre <= 1000000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 1000000)),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition answer_query_safety_wit_2 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (retval: Z) (PreH1 : (retval > t_pre)) (PreH2 : (retval = (A_pre + ((l_pre - 1 ) * B_pre ) ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= 1000000)) (PreH5 : (1 <= B_pre)) (PreH6 : (B_pre <= 1000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= 1000000)) (PreH9 : (1 <= t_pre)) (PreH10 : (t_pre <= 1000000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 1000000)),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition answer_query_safety_wit_3 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (ans: Z) (hi: Z) (retval: Z) (PreH1 : (retval <= t_pre)) (PreH2 : (retval = (A_pre + ((hi - 1 ) * B_pre ) ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= 1000000)) (PreH5 : (1 <= B_pre)) (PreH6 : (B_pre <= 1000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= 1000000)) (PreH9 : (1 <= t_pre)) (PreH10 : (t_pre <= 1000000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 1000000)) (PreH13 : (l_pre <= hi)) (PreH14 : (hi <= 2000000)) (PreH15 : (l_pre <= ans)) (PreH16 : (ans <= 2000000)) (PreH17 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "lo" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((hi * 2 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (hi * 2 )) ”
.

Definition answer_query_safety_wit_4 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (ans: Z) (hi: Z) (retval: Z) (PreH1 : (retval <= t_pre)) (PreH2 : (retval = (A_pre + ((hi - 1 ) * B_pre ) ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= 1000000)) (PreH5 : (1 <= B_pre)) (PreH6 : (B_pre <= 1000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= 1000000)) (PreH9 : (1 <= t_pre)) (PreH10 : (t_pre <= 1000000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 1000000)) (PreH13 : (l_pre <= hi)) (PreH14 : (hi <= 2000000)) (PreH15 : (l_pre <= ans)) (PreH16 : (ans <= 2000000)) (PreH17 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "lo" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition answer_query_safety_wit_5 :=
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= l_pre)) (PreH7 : (l_pre <= 1000000)) (PreH8 : (1 <= t_pre)) (PreH9 : (t_pre <= 1000000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 1000000)) (PreH12 : (l_pre <= lo)) (PreH13 : (lo <= ans)) (PreH14 : (ans <= hi)) (PreH15 : (hi <= 2000000)) (PreH16 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
) \/
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= l_pre)) (PreH7 : (l_pre <= 1000000)) (PreH8 : (1 <= t_pre)) (PreH9 : (t_pre <= 1000000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 1000000)) (PreH12 : (l_pre <= lo)) (PreH13 : (lo <= ans)) (PreH14 : (ans <= hi)) (PreH15 : (hi <= 2000000)) (PreH16 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
).

Definition answer_query_safety_wit_5_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= l_pre)) (PreH7 : (l_pre <= 1000000)) (PreH8 : (1 <= t_pre)) (PreH9 : (t_pre <= 1000000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 1000000)) (PreH12 : (l_pre <= lo)) (PreH13 : (lo <= ans)) (PreH14 : (ans <= hi)) (PreH15 : (hi <= 2000000)) (PreH16 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT64_MAX) ”
.

Definition answer_query_safety_wit_5_split_goal_2 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= l_pre)) (PreH7 : (l_pre <= 1000000)) (PreH8 : (1 <= t_pre)) (PreH9 : (t_pre <= 1000000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 1000000)) (PreH12 : (l_pre <= lo)) (PreH13 : (lo <= ans)) (PreH14 : (ans <= hi)) (PreH15 : (hi <= 2000000)) (PreH16 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((INT64_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
.

Definition answer_query_safety_wit_6 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= l_pre)) (PreH7 : (l_pre <= 1000000)) (PreH8 : (1 <= t_pre)) (PreH9 : (t_pre <= 1000000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 1000000)) (PreH12 : (l_pre <= lo)) (PreH13 : (lo <= ans)) (PreH14 : (ans <= hi)) (PreH15 : (hi <= 2000000)) (PreH16 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((((hi - lo ) + 1 ) <> (INT64_MIN)) \/ (2 <> (-1))) ”
  &&  “ (2 <> 0) ”
.

Definition answer_query_safety_wit_7 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= l_pre)) (PreH7 : (l_pre <= 1000000)) (PreH8 : (1 <= t_pre)) (PreH9 : (t_pre <= 1000000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 1000000)) (PreH12 : (l_pre <= lo)) (PreH13 : (lo <= ans)) (PreH14 : (ans <= hi)) (PreH15 : (hi <= 2000000)) (PreH16 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (((hi - lo ) + 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((hi - lo ) + 1 )) ”
.

Definition answer_query_safety_wit_8 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= l_pre)) (PreH7 : (l_pre <= 1000000)) (PreH8 : (1 <= t_pre)) (PreH9 : (t_pre <= 1000000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 1000000)) (PreH12 : (l_pre <= lo)) (PreH13 : (lo <= ans)) (PreH14 : (ans <= hi)) (PreH15 : (hi <= 2000000)) (PreH16 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((hi - lo ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (hi - lo )) ”
.

Definition answer_query_safety_wit_9 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= l_pre)) (PreH7 : (l_pre <= 1000000)) (PreH8 : (1 <= t_pre)) (PreH9 : (t_pre <= 1000000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 1000000)) (PreH12 : (l_pre <= lo)) (PreH13 : (lo <= ans)) (PreH14 : (ans <= hi)) (PreH15 : (hi <= 2000000)) (PreH16 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition answer_query_safety_wit_10 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= l_pre)) (PreH7 : (l_pre <= 1000000)) (PreH8 : (1 <= t_pre)) (PreH9 : (t_pre <= 1000000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 1000000)) (PreH12 : (l_pre <= lo)) (PreH13 : (lo <= ans)) (PreH14 : (ans <= hi)) (PreH15 : (hi <= 2000000)) (PreH16 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition answer_query_safety_wit_11 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (((((A_pre + ((l_pre - 1 ) * B_pre ) ) + A_pre ) + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ) * (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - l_pre ) + 1 ) ) ÷ 2 ))) (PreH2 : (retval <= t_pre)) (PreH3 : (retval = (A_pre + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ))) (PreH4 : (lo < hi)) (PreH5 : (1 <= A_pre)) (PreH6 : (A_pre <= 1000000)) (PreH7 : (1 <= B_pre)) (PreH8 : (B_pre <= 1000000)) (PreH9 : (1 <= l_pre)) (PreH10 : (l_pre <= 1000000)) (PreH11 : (1 <= t_pre)) (PreH12 : (t_pre <= 1000000)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 1000000)) (PreH15 : (l_pre <= lo)) (PreH16 : (lo <= ans)) (PreH17 : (ans <= hi)) (PreH18 : (hi <= 2000000)) (PreH19 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((t_pre * m_pre ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (t_pre * m_pre )) ”
.

Definition answer_query_safety_wit_12 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (retval: Z) (PreH1 : (retval > t_pre)) (PreH2 : (retval = (A_pre + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ))) (PreH3 : (lo < hi)) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= 1000000)) (PreH6 : (1 <= B_pre)) (PreH7 : (B_pre <= 1000000)) (PreH8 : (1 <= l_pre)) (PreH9 : (l_pre <= 1000000)) (PreH10 : (1 <= t_pre)) (PreH11 : (t_pre <= 1000000)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 1000000)) (PreH14 : (l_pre <= lo)) (PreH15 : (lo <= ans)) (PreH16 : (ans <= hi)) (PreH17 : (hi <= 2000000)) (PreH18 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
.

Definition answer_query_safety_wit_13 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (retval: Z) (PreH1 : (retval > t_pre)) (PreH2 : (retval = (A_pre + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ))) (PreH3 : (lo < hi)) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= 1000000)) (PreH6 : (1 <= B_pre)) (PreH7 : (B_pre <= 1000000)) (PreH8 : (1 <= l_pre)) (PreH9 : (l_pre <= 1000000)) (PreH10 : (1 <= t_pre)) (PreH11 : (t_pre <= 1000000)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 1000000)) (PreH14 : (l_pre <= lo)) (PreH15 : (lo <= ans)) (PreH16 : (ans <= hi)) (PreH17 : (hi <= 2000000)) (PreH18 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition answer_query_safety_wit_14 :=
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 > (t_pre * m_pre ))) (PreH2 : (retval_2 = (((((A_pre + ((l_pre - 1 ) * B_pre ) ) + A_pre ) + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ) * (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - l_pre ) + 1 ) ) ÷ 2 ))) (PreH3 : (retval <= t_pre)) (PreH4 : (retval = (A_pre + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ))) (PreH5 : (lo < hi)) (PreH6 : (1 <= A_pre)) (PreH7 : (A_pre <= 1000000)) (PreH8 : (1 <= B_pre)) (PreH9 : (B_pre <= 1000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= 1000000)) (PreH12 : (1 <= t_pre)) (PreH13 : (t_pre <= 1000000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 1000000)) (PreH16 : (l_pre <= lo)) (PreH17 : (lo <= ans)) (PreH18 : (ans <= hi)) (PreH19 : (hi <= 2000000)) (PreH20 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
) \/
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 > (t_pre * m_pre ))) (PreH2 : (retval_2 = (((((A_pre + ((l_pre - 1 ) * B_pre ) ) + A_pre ) + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ) * (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - l_pre ) + 1 ) ) ÷ 2 ))) (PreH3 : (retval <= t_pre)) (PreH4 : (retval = (A_pre + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ))) (PreH5 : (lo < hi)) (PreH6 : (1 <= A_pre)) (PreH7 : (A_pre <= 1000000)) (PreH8 : (1 <= B_pre)) (PreH9 : (B_pre <= 1000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= 1000000)) (PreH12 : (1 <= t_pre)) (PreH13 : (t_pre <= 1000000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 1000000)) (PreH16 : (l_pre <= lo)) (PreH17 : (lo <= ans)) (PreH18 : (ans <= hi)) (PreH19 : (hi <= 2000000)) (PreH20 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
).

Definition answer_query_safety_wit_14_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 > (t_pre * m_pre ))) (PreH2 : (retval_2 = (((((A_pre + ((l_pre - 1 ) * B_pre ) ) + A_pre ) + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ) * (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - l_pre ) + 1 ) ) ÷ 2 ))) (PreH3 : (retval <= t_pre)) (PreH4 : (retval = (A_pre + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ))) (PreH5 : (lo < hi)) (PreH6 : (1 <= A_pre)) (PreH7 : (A_pre <= 1000000)) (PreH8 : (1 <= B_pre)) (PreH9 : (B_pre <= 1000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= 1000000)) (PreH12 : (1 <= t_pre)) (PreH13 : (t_pre <= 1000000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 1000000)) (PreH16 : (l_pre <= lo)) (PreH17 : (lo <= ans)) (PreH18 : (ans <= hi)) (PreH19 : (hi <= 2000000)) (PreH20 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= INT64_MAX) ”
.

Definition answer_query_safety_wit_14_split_goal_2 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 > (t_pre * m_pre ))) (PreH2 : (retval_2 = (((((A_pre + ((l_pre - 1 ) * B_pre ) ) + A_pre ) + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ) * (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - l_pre ) + 1 ) ) ÷ 2 ))) (PreH3 : (retval <= t_pre)) (PreH4 : (retval = (A_pre + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ))) (PreH5 : (lo < hi)) (PreH6 : (1 <= A_pre)) (PreH7 : (A_pre <= 1000000)) (PreH8 : (1 <= B_pre)) (PreH9 : (B_pre <= 1000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= 1000000)) (PreH12 : (1 <= t_pre)) (PreH13 : (t_pre <= 1000000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 1000000)) (PreH16 : (l_pre <= lo)) (PreH17 : (lo <= ans)) (PreH18 : (ans <= hi)) (PreH19 : (hi <= 2000000)) (PreH20 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((INT64_MIN) <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
.

Definition answer_query_safety_wit_15 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 > (t_pre * m_pre ))) (PreH2 : (retval_2 = (((((A_pre + ((l_pre - 1 ) * B_pre ) ) + A_pre ) + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ) * (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - l_pre ) + 1 ) ) ÷ 2 ))) (PreH3 : (retval <= t_pre)) (PreH4 : (retval = (A_pre + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ))) (PreH5 : (lo < hi)) (PreH6 : (1 <= A_pre)) (PreH7 : (A_pre <= 1000000)) (PreH8 : (1 <= B_pre)) (PreH9 : (B_pre <= 1000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= 1000000)) (PreH12 : (1 <= t_pre)) (PreH13 : (t_pre <= 1000000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 1000000)) (PreH16 : (l_pre <= lo)) (PreH17 : (lo <= ans)) (PreH18 : (ans <= hi)) (PreH19 : (hi <= 2000000)) (PreH20 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition answer_query_entail_wit_1 :=
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (retval: Z) (PreH1 : (retval <= t_pre)) (PreH2 : (retval = (A_pre + ((l_pre - 1 ) * B_pre ) ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= 1000000)) (PreH5 : (1 <= B_pre)) (PreH6 : (B_pre <= 1000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= 1000000)) (PreH9 : (1 <= t_pre)) (PreH10 : (t_pre <= 1000000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 1000000)),
  TT && emp 
|--
  EX (ans: Z),
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= l_pre) ”
  &&  “ (l_pre <= 1000000) ”
  &&  “ (1 <= t_pre) ”
  &&  “ (t_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (l_pre <= l_pre) ”
  &&  “ (l_pre <= 2000000) ”
  &&  “ (l_pre <= ans) ”
  &&  “ (ans <= 2000000) ”
  &&  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans ) ”
  &&  emp
) \/
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (retval: Z) (PreH1 : (retval <= t_pre)) (PreH2 : (retval = (A_pre + ((l_pre - 1 ) * B_pre ) ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= 1000000)) (PreH5 : (1 <= B_pre)) (PreH6 : (B_pre <= 1000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= 1000000)) (PreH9 : (1 <= t_pre)) (PreH10 : (t_pre <= 1000000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 1000000)),
  TT && emp 
|--
  EX (ans: Z),
  “ (l_pre <= l_pre) ”
  &&  “ (l_pre <= 2000000) ”
  &&  “ (l_pre <= ans) ”
  &&  “ (ans <= 2000000) ”
  &&  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans ) ”
  &&  emp
).

Definition answer_query_entail_wit_2 :=
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (ans_2: Z) (hi: Z) (retval: Z) (PreH1 : (retval <= t_pre)) (PreH2 : (retval = (A_pre + ((hi - 1 ) * B_pre ) ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= 1000000)) (PreH5 : (1 <= B_pre)) (PreH6 : (B_pre <= 1000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= 1000000)) (PreH9 : (1 <= t_pre)) (PreH10 : (t_pre <= 1000000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 1000000)) (PreH13 : (l_pre <= hi)) (PreH14 : (hi <= 2000000)) (PreH15 : (l_pre <= ans_2)) (PreH16 : (ans_2 <= 2000000)) (PreH17 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans_2 )),
  TT && emp 
|--
  EX (ans: Z),
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= l_pre) ”
  &&  “ (l_pre <= 1000000) ”
  &&  “ (1 <= t_pre) ”
  &&  “ (t_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (l_pre <= (hi * 2 )) ”
  &&  “ ((hi * 2 ) <= 2000000) ”
  &&  “ (l_pre <= ans) ”
  &&  “ (ans <= 2000000) ”
  &&  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans ) ”
  &&  emp
) \/
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (ans_2: Z) (hi: Z) (retval: Z) (PreH1 : (retval <= t_pre)) (PreH2 : (retval = (A_pre + ((hi - 1 ) * B_pre ) ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= 1000000)) (PreH5 : (1 <= B_pre)) (PreH6 : (B_pre <= 1000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= 1000000)) (PreH9 : (1 <= t_pre)) (PreH10 : (t_pre <= 1000000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 1000000)) (PreH13 : (l_pre <= hi)) (PreH14 : (hi <= 2000000)) (PreH15 : (l_pre <= ans_2)) (PreH16 : (ans_2 <= 2000000)) (PreH17 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans_2 )),
  TT && emp 
|--
  EX (ans: Z),
  “ (l_pre <= (hi * 2 )) ”
  &&  “ ((hi * 2 ) <= 2000000) ”
  &&  “ (l_pre <= ans) ”
  &&  “ (ans <= 2000000) ”
  &&  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans ) ”
  &&  emp
).

Definition answer_query_entail_wit_3 :=
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (ans_2: Z) (hi: Z) (retval: Z) (PreH1 : (retval > t_pre)) (PreH2 : (retval = (A_pre + ((hi - 1 ) * B_pre ) ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= 1000000)) (PreH5 : (1 <= B_pre)) (PreH6 : (B_pre <= 1000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= 1000000)) (PreH9 : (1 <= t_pre)) (PreH10 : (t_pre <= 1000000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 1000000)) (PreH13 : (l_pre <= hi)) (PreH14 : (hi <= 2000000)) (PreH15 : (l_pre <= ans_2)) (PreH16 : (ans_2 <= 2000000)) (PreH17 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans_2 )),
  TT && emp 
|--
  EX (ans: Z),
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= l_pre) ”
  &&  “ (l_pre <= 1000000) ”
  &&  “ (1 <= t_pre) ”
  &&  “ (t_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (l_pre <= l_pre) ”
  &&  “ (l_pre <= ans) ”
  &&  “ (ans <= hi) ”
  &&  “ (hi <= 2000000) ”
  &&  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans ) ”
  &&  emp
) \/
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (ans_2: Z) (hi: Z) (retval: Z) (PreH1 : (retval > t_pre)) (PreH2 : (retval = (A_pre + ((hi - 1 ) * B_pre ) ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= 1000000)) (PreH5 : (1 <= B_pre)) (PreH6 : (B_pre <= 1000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= 1000000)) (PreH9 : (1 <= t_pre)) (PreH10 : (t_pre <= 1000000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 1000000)) (PreH13 : (l_pre <= hi)) (PreH14 : (hi <= 2000000)) (PreH15 : (l_pre <= ans_2)) (PreH16 : (ans_2 <= 2000000)) (PreH17 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans_2 )),
  TT && emp 
|--
  EX (ans: Z),
  “ (l_pre <= l_pre) ”
  &&  “ (l_pre <= ans) ”
  &&  “ (ans <= hi) ”
  &&  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans ) ”
  &&  emp
).

Definition answer_query_entail_wit_4 :=
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (ans_2: Z) (lo: Z) (hi: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= 1000000)) (PreH7 : (1 <= t_pre)) (PreH8 : (t_pre <= 1000000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 1000000)) (PreH11 : (l_pre <= lo)) (PreH12 : (lo <= ans_2)) (PreH13 : (ans_2 <= hi)) (PreH14 : (hi <= 2000000)) (PreH15 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans_2 )),
  TT && emp 
|--
  EX (ans: Z),
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= l_pre) ”
  &&  “ (l_pre <= 1000000) ”
  &&  “ (1 <= t_pre) ”
  &&  “ (t_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (l_pre <= lo) ”
  &&  “ (lo <= ans) ”
  &&  “ (ans <= hi) ”
  &&  “ (hi <= 2000000) ”
  &&  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans ) ”
  &&  emp
) \/
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (ans_2: Z) (lo: Z) (hi: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= 1000000)) (PreH7 : (1 <= t_pre)) (PreH8 : (t_pre <= 1000000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 1000000)) (PreH11 : (l_pre <= lo)) (PreH12 : (lo <= ans_2)) (PreH13 : (ans_2 <= hi)) (PreH14 : (hi <= 2000000)) (PreH15 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans_2 )),
  TT && emp 
|--
  EX (ans: Z),
  “ (lo <= ans) ”
  &&  “ (ans <= hi) ”
  &&  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans ) ”
  &&  emp
).

Definition answer_query_entail_wit_5_1 :=
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans_2: Z) (lo: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <= (t_pre * m_pre ))) (PreH2 : (retval_2 = (((((A_pre + ((l_pre - 1 ) * B_pre ) ) + A_pre ) + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ) * (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - l_pre ) + 1 ) ) ÷ 2 ))) (PreH3 : (retval <= t_pre)) (PreH4 : (retval = (A_pre + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ))) (PreH5 : (lo < hi)) (PreH6 : (1 <= A_pre)) (PreH7 : (A_pre <= 1000000)) (PreH8 : (1 <= B_pre)) (PreH9 : (B_pre <= 1000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= 1000000)) (PreH12 : (1 <= t_pre)) (PreH13 : (t_pre <= 1000000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 1000000)) (PreH16 : (l_pre <= lo)) (PreH17 : (lo <= ans_2)) (PreH18 : (ans_2 <= hi)) (PreH19 : (hi <= 2000000)) (PreH20 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans_2 )),
  TT && emp 
|--
  EX (ans: Z),
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= l_pre) ”
  &&  “ (l_pre <= 1000000) ”
  &&  “ (1 <= t_pre) ”
  &&  “ (t_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (l_pre <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= ans) ”
  &&  “ (ans <= hi) ”
  &&  “ (hi <= 2000000) ”
  &&  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans ) ”
  &&  emp
) \/
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans_2: Z) (lo: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <= (t_pre * m_pre ))) (PreH2 : (retval_2 = (((((A_pre + ((l_pre - 1 ) * B_pre ) ) + A_pre ) + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ) * (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - l_pre ) + 1 ) ) ÷ 2 ))) (PreH3 : (retval <= t_pre)) (PreH4 : (retval = (A_pre + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ))) (PreH5 : (lo < hi)) (PreH6 : (1 <= A_pre)) (PreH7 : (A_pre <= 1000000)) (PreH8 : (1 <= B_pre)) (PreH9 : (B_pre <= 1000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= 1000000)) (PreH12 : (1 <= t_pre)) (PreH13 : (t_pre <= 1000000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 1000000)) (PreH16 : (l_pre <= lo)) (PreH17 : (lo <= ans_2)) (PreH18 : (ans_2 <= hi)) (PreH19 : (hi <= 2000000)) (PreH20 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans_2 )),
  TT && emp 
|--
  EX (ans: Z),
  “ (l_pre <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= ans) ”
  &&  “ (ans <= hi) ”
  &&  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans ) ”
  &&  emp
).

Definition answer_query_entail_wit_5_2 :=
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans_2: Z) (lo: Z) (retval: Z) (PreH1 : (retval > t_pre)) (PreH2 : (retval = (A_pre + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ))) (PreH3 : (lo < hi)) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= 1000000)) (PreH6 : (1 <= B_pre)) (PreH7 : (B_pre <= 1000000)) (PreH8 : (1 <= l_pre)) (PreH9 : (l_pre <= 1000000)) (PreH10 : (1 <= t_pre)) (PreH11 : (t_pre <= 1000000)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 1000000)) (PreH14 : (l_pre <= lo)) (PreH15 : (lo <= ans_2)) (PreH16 : (ans_2 <= hi)) (PreH17 : (hi <= 2000000)) (PreH18 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans_2 )),
  TT && emp 
|--
  EX (ans: Z),
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= l_pre) ”
  &&  “ (l_pre <= 1000000) ”
  &&  “ (1 <= t_pre) ”
  &&  “ (t_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (l_pre <= lo) ”
  &&  “ (lo <= ans) ”
  &&  “ (ans <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
  &&  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= 2000000) ”
  &&  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans ) ”
  &&  emp
) \/
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans_2: Z) (lo: Z) (retval: Z) (PreH1 : (retval > t_pre)) (PreH2 : (retval = (A_pre + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ))) (PreH3 : (lo < hi)) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= 1000000)) (PreH6 : (1 <= B_pre)) (PreH7 : (B_pre <= 1000000)) (PreH8 : (1 <= l_pre)) (PreH9 : (l_pre <= 1000000)) (PreH10 : (1 <= t_pre)) (PreH11 : (t_pre <= 1000000)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 1000000)) (PreH14 : (l_pre <= lo)) (PreH15 : (lo <= ans_2)) (PreH16 : (ans_2 <= hi)) (PreH17 : (hi <= 2000000)) (PreH18 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans_2 )),
  TT && emp 
|--
  EX (ans: Z),
  “ (lo <= ans) ”
  &&  “ (ans <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
  &&  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= 2000000) ”
  &&  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans ) ”
  &&  emp
).

Definition answer_query_entail_wit_5_3 :=
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans_2: Z) (lo: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 > (t_pre * m_pre ))) (PreH2 : (retval_2 = (((((A_pre + ((l_pre - 1 ) * B_pre ) ) + A_pre ) + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ) * (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - l_pre ) + 1 ) ) ÷ 2 ))) (PreH3 : (retval <= t_pre)) (PreH4 : (retval = (A_pre + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ))) (PreH5 : (lo < hi)) (PreH6 : (1 <= A_pre)) (PreH7 : (A_pre <= 1000000)) (PreH8 : (1 <= B_pre)) (PreH9 : (B_pre <= 1000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= 1000000)) (PreH12 : (1 <= t_pre)) (PreH13 : (t_pre <= 1000000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 1000000)) (PreH16 : (l_pre <= lo)) (PreH17 : (lo <= ans_2)) (PreH18 : (ans_2 <= hi)) (PreH19 : (hi <= 2000000)) (PreH20 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans_2 )),
  TT && emp 
|--
  EX (ans: Z),
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= l_pre) ”
  &&  “ (l_pre <= 1000000) ”
  &&  “ (1 <= t_pre) ”
  &&  “ (t_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (l_pre <= lo) ”
  &&  “ (lo <= ans) ”
  &&  “ (ans <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
  &&  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= 2000000) ”
  &&  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans ) ”
  &&  emp
) \/
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans_2: Z) (lo: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 > (t_pre * m_pre ))) (PreH2 : (retval_2 = (((((A_pre + ((l_pre - 1 ) * B_pre ) ) + A_pre ) + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ) * (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - l_pre ) + 1 ) ) ÷ 2 ))) (PreH3 : (retval <= t_pre)) (PreH4 : (retval = (A_pre + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ))) (PreH5 : (lo < hi)) (PreH6 : (1 <= A_pre)) (PreH7 : (A_pre <= 1000000)) (PreH8 : (1 <= B_pre)) (PreH9 : (B_pre <= 1000000)) (PreH10 : (1 <= l_pre)) (PreH11 : (l_pre <= 1000000)) (PreH12 : (1 <= t_pre)) (PreH13 : (t_pre <= 1000000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 1000000)) (PreH16 : (l_pre <= lo)) (PreH17 : (lo <= ans_2)) (PreH18 : (ans_2 <= hi)) (PreH19 : (hi <= 2000000)) (PreH20 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans_2 )),
  TT && emp 
|--
  EX (ans: Z),
  “ (lo <= ans) ”
  &&  “ (ans <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
  &&  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= 2000000) ”
  &&  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans ) ”
  &&  emp
).

Definition answer_query_return_wit_1 :=
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (PreH1 : (lo >= hi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= l_pre)) (PreH7 : (l_pre <= 1000000)) (PreH8 : (1 <= t_pre)) (PreH9 : (t_pre <= 1000000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 1000000)) (PreH12 : (l_pre <= lo)) (PreH13 : (lo <= ans)) (PreH14 : (ans <= hi)) (PreH15 : (hi <= 2000000)) (PreH16 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  TT && emp 
|--
  “ ((-1) <= lo) ”
  &&  “ (lo <= 2000000) ”
  &&  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) lo ) ”
  &&  emp
) \/
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (PreH1 : (lo >= hi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= l_pre)) (PreH7 : (l_pre <= 1000000)) (PreH8 : (1 <= t_pre)) (PreH9 : (t_pre <= 1000000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 1000000)) (PreH12 : (l_pre <= lo)) (PreH13 : (lo <= ans)) (PreH14 : (ans <= hi)) (PreH15 : (hi <= 2000000)) (PreH16 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  TT && emp 
|--
  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) lo ) ”
  &&  emp
).

Definition answer_query_return_wit_1_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (PreH1 : (lo >= hi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= l_pre)) (PreH7 : (l_pre <= 1000000)) (PreH8 : (1 <= t_pre)) (PreH9 : (t_pre <= 1000000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 1000000)) (PreH12 : (l_pre <= lo)) (PreH13 : (lo <= ans)) (PreH14 : (ans <= hi)) (PreH15 : (hi <= 2000000)) (PreH16 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) lo )
.

Definition answer_query_return_wit_2 :=
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (retval: Z) (PreH1 : (retval > t_pre)) (PreH2 : (retval = (A_pre + ((l_pre - 1 ) * B_pre ) ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= 1000000)) (PreH5 : (1 <= B_pre)) (PreH6 : (B_pre <= 1000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= 1000000)) (PreH9 : (1 <= t_pre)) (PreH10 : (t_pre <= 1000000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 1000000)),
  TT && emp 
|--
  “ ((-1) <= (-1)) ”
  &&  “ ((-1) <= 2000000) ”
  &&  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) (-1) ) ”
  &&  emp
) \/
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (retval: Z) (PreH1 : (retval > t_pre)) (PreH2 : (retval = (A_pre + ((l_pre - 1 ) * B_pre ) ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= 1000000)) (PreH5 : (1 <= B_pre)) (PreH6 : (B_pre <= 1000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= 1000000)) (PreH9 : (1 <= t_pre)) (PreH10 : (t_pre <= 1000000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 1000000)),
  TT && emp 
|--
  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) (-1) ) ”
  &&  emp
).

Definition answer_query_return_wit_2_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (retval: Z) (PreH1 : (retval > t_pre)) (PreH2 : (retval = (A_pre + ((l_pre - 1 ) * B_pre ) ))) (PreH3 : (1 <= A_pre)) (PreH4 : (A_pre <= 1000000)) (PreH5 : (1 <= B_pre)) (PreH6 : (B_pre <= 1000000)) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre <= 1000000)) (PreH9 : (1 <= t_pre)) (PreH10 : (t_pre <= 1000000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 1000000)),
  (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) (-1) )
.

Definition answer_query_partial_solve_wit_1_pure :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= 1000000)) (PreH7 : (1 <= t_pre)) (PreH8 : (t_pre <= 1000000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 1000000)),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= l_pre) ”
  &&  “ (l_pre <= 2000000) ”
.

Definition answer_query_partial_solve_wit_1_aux :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= 1000000)) (PreH7 : (1 <= t_pre)) (PreH8 : (t_pre <= 1000000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 1000000)),
  TT && emp 
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= l_pre) ”
  &&  “ (l_pre <= 2000000) ”
  &&  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= l_pre) ”
  &&  “ (l_pre <= 1000000) ”
  &&  “ (1 <= t_pre) ”
  &&  “ (t_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  emp
.

Definition answer_query_partial_solve_wit_1 := answer_query_partial_solve_wit_1_pure -> answer_query_partial_solve_wit_1_aux.

Definition answer_query_partial_solve_wit_2_pure :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (ans: Z) (hi: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= 1000000)) (PreH7 : (1 <= t_pre)) (PreH8 : (t_pre <= 1000000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 1000000)) (PreH11 : (l_pre <= hi)) (PreH12 : (hi <= 2000000)) (PreH13 : (l_pre <= ans)) (PreH14 : (ans <= 2000000)) (PreH15 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "lo" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= hi) ”
  &&  “ (hi <= 2000000) ”
.

Definition answer_query_partial_solve_wit_2_aux :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (ans: Z) (hi: Z) (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= l_pre)) (PreH6 : (l_pre <= 1000000)) (PreH7 : (1 <= t_pre)) (PreH8 : (t_pre <= 1000000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 1000000)) (PreH11 : (l_pre <= hi)) (PreH12 : (hi <= 2000000)) (PreH13 : (l_pre <= ans)) (PreH14 : (ans <= 2000000)) (PreH15 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  TT && emp 
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= hi) ”
  &&  “ (hi <= 2000000) ”
  &&  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= l_pre) ”
  &&  “ (l_pre <= 1000000) ”
  &&  “ (1 <= t_pre) ”
  &&  “ (t_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (l_pre <= hi) ”
  &&  “ (hi <= 2000000) ”
  &&  “ (l_pre <= ans) ”
  &&  “ (ans <= 2000000) ”
  &&  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans ) ”
  &&  emp
.

Definition answer_query_partial_solve_wit_2 := answer_query_partial_solve_wit_2_pure -> answer_query_partial_solve_wit_2_aux.

Definition answer_query_partial_solve_wit_3_pure :=
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= l_pre)) (PreH7 : (l_pre <= 1000000)) (PreH8 : (1 <= t_pre)) (PreH9 : (t_pre <= 1000000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 1000000)) (PreH12 : (l_pre <= lo)) (PreH13 : (lo <= ans)) (PreH14 : (ans <= hi)) (PreH15 : (hi <= 2000000)) (PreH16 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= 2000000) ”
  &&  “ (1 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
) \/
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (PreH1 : (hi <= INT64_MAX)) (PreH2 : (lo <= INT64_MAX)) (PreH3 : (m_pre <= INT64_MAX)) (PreH4 : (t_pre <= INT64_MAX)) (PreH5 : (l_pre <= INT64_MAX)) (PreH6 : (B_pre <= INT64_MAX)) (PreH7 : (A_pre <= INT64_MAX)) (PreH8 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT64_MAX)) (PreH9 : (hi >= INT64_MIN)) (PreH10 : (lo >= INT64_MIN)) (PreH11 : (m_pre >= INT64_MIN)) (PreH12 : (t_pre >= INT64_MIN)) (PreH13 : (l_pre >= INT64_MIN)) (PreH14 : (B_pre >= INT64_MIN)) (PreH15 : (A_pre >= INT64_MIN)) (PreH16 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) >= INT64_MIN)) (PreH17 : (lo < hi)) (PreH18 : (1 <= A_pre)) (PreH19 : (A_pre <= 1000000)) (PreH20 : (1 <= B_pre)) (PreH21 : (B_pre <= 1000000)) (PreH22 : (1 <= l_pre)) (PreH23 : (l_pre <= 1000000)) (PreH24 : (1 <= t_pre)) (PreH25 : (t_pre <= 1000000)) (PreH26 : (1 <= m_pre)) (PreH27 : (m_pre <= 1000000)) (PreH28 : (l_pre <= lo)) (PreH29 : (lo <= ans)) (PreH30 : (ans <= hi)) (PreH31 : (hi <= 2000000)) (PreH32 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (1 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= 2000000) ”
).

Definition answer_query_partial_solve_wit_3_pure_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (PreH1 : (hi <= INT64_MAX)) (PreH2 : (lo <= INT64_MAX)) (PreH3 : (m_pre <= INT64_MAX)) (PreH4 : (t_pre <= INT64_MAX)) (PreH5 : (l_pre <= INT64_MAX)) (PreH6 : (B_pre <= INT64_MAX)) (PreH7 : (A_pre <= INT64_MAX)) (PreH8 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT64_MAX)) (PreH9 : (hi >= INT64_MIN)) (PreH10 : (lo >= INT64_MIN)) (PreH11 : (m_pre >= INT64_MIN)) (PreH12 : (t_pre >= INT64_MIN)) (PreH13 : (l_pre >= INT64_MIN)) (PreH14 : (B_pre >= INT64_MIN)) (PreH15 : (A_pre >= INT64_MIN)) (PreH16 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) >= INT64_MIN)) (PreH17 : (lo < hi)) (PreH18 : (1 <= A_pre)) (PreH19 : (A_pre <= 1000000)) (PreH20 : (1 <= B_pre)) (PreH21 : (B_pre <= 1000000)) (PreH22 : (1 <= l_pre)) (PreH23 : (l_pre <= 1000000)) (PreH24 : (1 <= t_pre)) (PreH25 : (t_pre <= 1000000)) (PreH26 : (1 <= m_pre)) (PreH27 : (m_pre <= 1000000)) (PreH28 : (l_pre <= lo)) (PreH29 : (lo <= ans)) (PreH30 : (ans <= hi)) (PreH31 : (hi <= 2000000)) (PreH32 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (1 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
.

Definition answer_query_partial_solve_wit_3_pure_split_goal_2 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (PreH1 : (hi <= INT64_MAX)) (PreH2 : (lo <= INT64_MAX)) (PreH3 : (m_pre <= INT64_MAX)) (PreH4 : (t_pre <= INT64_MAX)) (PreH5 : (l_pre <= INT64_MAX)) (PreH6 : (B_pre <= INT64_MAX)) (PreH7 : (A_pre <= INT64_MAX)) (PreH8 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT64_MAX)) (PreH9 : (hi >= INT64_MIN)) (PreH10 : (lo >= INT64_MIN)) (PreH11 : (m_pre >= INT64_MIN)) (PreH12 : (t_pre >= INT64_MIN)) (PreH13 : (l_pre >= INT64_MIN)) (PreH14 : (B_pre >= INT64_MIN)) (PreH15 : (A_pre >= INT64_MIN)) (PreH16 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) >= INT64_MIN)) (PreH17 : (lo < hi)) (PreH18 : (1 <= A_pre)) (PreH19 : (A_pre <= 1000000)) (PreH20 : (1 <= B_pre)) (PreH21 : (B_pre <= 1000000)) (PreH22 : (1 <= l_pre)) (PreH23 : (l_pre <= 1000000)) (PreH24 : (1 <= t_pre)) (PreH25 : (t_pre <= 1000000)) (PreH26 : (1 <= m_pre)) (PreH27 : (m_pre <= 1000000)) (PreH28 : (l_pre <= lo)) (PreH29 : (lo <= ans)) (PreH30 : (ans <= hi)) (PreH31 : (hi <= 2000000)) (PreH32 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= 2000000) ”
.

Definition answer_query_partial_solve_wit_3_aux :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= l_pre)) (PreH7 : (l_pre <= 1000000)) (PreH8 : (1 <= t_pre)) (PreH9 : (t_pre <= 1000000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 1000000)) (PreH12 : (l_pre <= lo)) (PreH13 : (lo <= ans)) (PreH14 : (ans <= hi)) (PreH15 : (hi <= 2000000)) (PreH16 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  TT && emp 
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= 2000000) ”
  &&  “ (1 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
  &&  “ (lo < hi) ”
  &&  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= l_pre) ”
  &&  “ (l_pre <= 1000000) ”
  &&  “ (1 <= t_pre) ”
  &&  “ (t_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (l_pre <= lo) ”
  &&  “ (lo <= ans) ”
  &&  “ (ans <= hi) ”
  &&  “ (hi <= 2000000) ”
  &&  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans ) ”
  &&  emp
.

Definition answer_query_partial_solve_wit_3 := answer_query_partial_solve_wit_3_pure -> answer_query_partial_solve_wit_3_aux.

Definition answer_query_partial_solve_wit_4_pure :=
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (retval: Z) (PreH1 : (retval <= t_pre)) (PreH2 : (retval = (A_pre + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ))) (PreH3 : (lo < hi)) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= 1000000)) (PreH6 : (1 <= B_pre)) (PreH7 : (B_pre <= 1000000)) (PreH8 : (1 <= l_pre)) (PreH9 : (l_pre <= 1000000)) (PreH10 : (1 <= t_pre)) (PreH11 : (t_pre <= 1000000)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 1000000)) (PreH14 : (l_pre <= lo)) (PreH15 : (lo <= ans)) (PreH16 : (ans <= hi)) (PreH17 : (hi <= 2000000)) (PreH18 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= l_pre) ”
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= 2000000) ”
  &&  “ (l_pre <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
) \/
(
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (retval: Z) (PreH1 : (hi <= INT64_MAX)) (PreH2 : (lo <= INT64_MAX)) (PreH3 : (m_pre <= INT64_MAX)) (PreH4 : (t_pre <= INT64_MAX)) (PreH5 : (l_pre <= INT64_MAX)) (PreH6 : (B_pre <= INT64_MAX)) (PreH7 : (A_pre <= INT64_MAX)) (PreH8 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT64_MAX)) (PreH9 : (hi >= INT64_MIN)) (PreH10 : (lo >= INT64_MIN)) (PreH11 : (m_pre >= INT64_MIN)) (PreH12 : (t_pre >= INT64_MIN)) (PreH13 : (l_pre >= INT64_MIN)) (PreH14 : (B_pre >= INT64_MIN)) (PreH15 : (A_pre >= INT64_MIN)) (PreH16 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) >= INT64_MIN)) (PreH17 : (retval <= t_pre)) (PreH18 : (retval = (A_pre + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ))) (PreH19 : (lo < hi)) (PreH20 : (1 <= A_pre)) (PreH21 : (A_pre <= 1000000)) (PreH22 : (1 <= B_pre)) (PreH23 : (B_pre <= 1000000)) (PreH24 : (1 <= l_pre)) (PreH25 : (l_pre <= 1000000)) (PreH26 : (1 <= t_pre)) (PreH27 : (t_pre <= 1000000)) (PreH28 : (1 <= m_pre)) (PreH29 : (m_pre <= 1000000)) (PreH30 : (l_pre <= lo)) (PreH31 : (lo <= ans)) (PreH32 : (ans <= hi)) (PreH33 : (hi <= 2000000)) (PreH34 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (l_pre <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
).

Definition answer_query_partial_solve_wit_4_pure_split_goal_1 :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (retval: Z) (PreH1 : (hi <= INT64_MAX)) (PreH2 : (lo <= INT64_MAX)) (PreH3 : (m_pre <= INT64_MAX)) (PreH4 : (t_pre <= INT64_MAX)) (PreH5 : (l_pre <= INT64_MAX)) (PreH6 : (B_pre <= INT64_MAX)) (PreH7 : (A_pre <= INT64_MAX)) (PreH8 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT64_MAX)) (PreH9 : (hi >= INT64_MIN)) (PreH10 : (lo >= INT64_MIN)) (PreH11 : (m_pre >= INT64_MIN)) (PreH12 : (t_pre >= INT64_MIN)) (PreH13 : (l_pre >= INT64_MIN)) (PreH14 : (B_pre >= INT64_MIN)) (PreH15 : (A_pre >= INT64_MIN)) (PreH16 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) >= INT64_MIN)) (PreH17 : (retval <= t_pre)) (PreH18 : (retval = (A_pre + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ))) (PreH19 : (lo < hi)) (PreH20 : (1 <= A_pre)) (PreH21 : (A_pre <= 1000000)) (PreH22 : (1 <= B_pre)) (PreH23 : (B_pre <= 1000000)) (PreH24 : (1 <= l_pre)) (PreH25 : (l_pre <= 1000000)) (PreH26 : (1 <= t_pre)) (PreH27 : (t_pre <= 1000000)) (PreH28 : (1 <= m_pre)) (PreH29 : (m_pre <= 1000000)) (PreH30 : (l_pre <= lo)) (PreH31 : (lo <= ans)) (PreH32 : (ans <= hi)) (PreH33 : (hi <= 2000000)) (PreH34 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  ((( &( "mid" ) )) # Int64  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "t" ) )) # Int64  |-> t_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "lo" ) )) # Int64  |-> lo)
  **  ((( &( "hi" ) )) # Int64  |-> hi)
|--
  “ (l_pre <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
.

Definition answer_query_partial_solve_wit_4_aux :=
forall (A_pre: Z) (B_pre: Z) (l_pre: Z) (t_pre: Z) (m_pre: Z) (hi: Z) (ans: Z) (lo: Z) (retval: Z) (PreH1 : (retval <= t_pre)) (PreH2 : (retval = (A_pre + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) ))) (PreH3 : (lo < hi)) (PreH4 : (1 <= A_pre)) (PreH5 : (A_pre <= 1000000)) (PreH6 : (1 <= B_pre)) (PreH7 : (B_pre <= 1000000)) (PreH8 : (1 <= l_pre)) (PreH9 : (l_pre <= 1000000)) (PreH10 : (1 <= t_pre)) (PreH11 : (t_pre <= 1000000)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 1000000)) (PreH14 : (l_pre <= lo)) (PreH15 : (lo <= ans)) (PreH16 : (ans <= hi)) (PreH17 : (hi <= 2000000)) (PreH18 : (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans )),
  TT && emp 
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= l_pre) ”
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= 2000000) ”
  &&  “ (l_pre <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
  &&  “ (retval <= t_pre) ”
  &&  “ (retval = (A_pre + (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) * B_pre ) )) ”
  &&  “ (lo < hi) ”
  &&  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= l_pre) ”
  &&  “ (l_pre <= 1000000) ”
  &&  “ (1 <= t_pre) ”
  &&  “ (t_pre <= 1000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 1000000) ”
  &&  “ (l_pre <= lo) ”
  &&  “ (lo <= ans) ”
  &&  “ (ans <= hi) ”
  &&  “ (hi <= 2000000) ”
  &&  “ (QueryAnswer A_pre B_pre (pair ((pair (l_pre) (t_pre))) (m_pre)) ans ) ”
  &&  emp
.

Definition answer_query_partial_solve_wit_4 := answer_query_partial_solve_wit_4_pure -> answer_query_partial_solve_wit_4_aux.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (ql_pre: Z) (qt_pre: Z) (qm_pre: Z) (n_pre: Z) (out_pre: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((((1 <= (fst ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth i queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH8 : (n_pre = (Zlength (queries)))) (PreH9 : ((Zlength (left_limits)) = n_pre)) (PreH10 : ((Zlength (times)) = n_pre)) (PreH11 : ((Zlength (maxima)) = n_pre)) (PreH12 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> ((((Znth i_2 left_limits 0) = (fst ((fst ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth i_2 times 0) = (snd ((fst ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i_2 maxima 0) = (snd ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z))))))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "ql" ) )) # Ptr  |-> ql_pre)
  **  ((( &( "qt" ) )) # Ptr  |-> qt_pre)
  **  ((( &( "qm" ) )) # Ptr  |-> qm_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.full ql_pre n_pre left_limits )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.full_shape out_pre n_pre )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (ql_pre: Z) (qt_pre: Z) (qm_pre: Z) (n_pre: Z) (out_pre: Z) (result: (@list Z)) (i: Z) (retval: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((-1) <= retval)) (PreH2 : (retval <= 2000000)) (PreH3 : (QueryAnswer A_pre B_pre (pair ((pair ((Znth i left_limits 0)) ((Znth i times 0)))) ((Znth i maxima 0))) retval )) (PreH4 : (i < n_pre)) (PreH5 : (1 <= A_pre)) (PreH6 : (A_pre <= 1000000)) (PreH7 : (1 <= B_pre)) (PreH8 : (B_pre <= 1000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000)) (PreH11 : (n_pre = (Zlength (queries)))) (PreH12 : ((Zlength (left_limits)) = n_pre)) (PreH13 : ((Zlength (times)) = n_pre)) (PreH14 : ((Zlength (maxima)) = n_pre)) (PreH15 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : ((Zlength (result)) = i)) (PreH20 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) ))),
  (Int64Array.seg out_pre 0 (i + 1 ) (app (result) ((cons (retval) ((@nil Z))))) )
  **  (Int64Array.undef_seg out_pre (i + 1 ) n_pre )
  **  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full ql_pre n_pre left_limits )
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "ql" ) )) # Ptr  |-> ql_pre)
  **  ((( &( "qt" ) )) # Ptr  |-> qt_pre)
  **  ((( &( "qm" ) )) # Ptr  |-> qm_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (ql_pre: Z) (qt_pre: Z) (qm_pre: Z) (n_pre: Z) (out_pre: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((((1 <= (fst ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth i queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH8 : (n_pre = (Zlength (queries)))) (PreH9 : ((Zlength (left_limits)) = n_pre)) (PreH10 : ((Zlength (times)) = n_pre)) (PreH11 : ((Zlength (maxima)) = n_pre)) (PreH12 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> ((((Znth i_2 left_limits 0) = (fst ((fst ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth i_2 times 0) = (snd ((fst ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i_2 maxima 0) = (snd ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z))))))),
  (Int64Array.full ql_pre n_pre left_limits )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.full_shape out_pre n_pre )
|--
  EX (result: (@list Z)),
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (queries))) ”
  &&  “ ((Zlength (left_limits)) = n_pre) ”
  &&  “ ((Zlength (times)) = n_pre) ”
  &&  “ ((Zlength (maxima)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= n_pre) ”
  &&  “ ((Zlength (result)) = 0) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < 0)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) )) ”
  &&  (Int64Array.full ql_pre n_pre left_limits )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.seg out_pre 0 0 result )
  **  (Int64Array.undef_seg out_pre 0 n_pre )
) \/
(
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (n_pre: Z) (out_pre: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((((1 <= (fst ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth i queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH8 : (n_pre = (Zlength (queries)))) (PreH9 : ((Zlength (left_limits)) = n_pre)) (PreH10 : ((Zlength (times)) = n_pre)) (PreH11 : ((Zlength (maxima)) = n_pre)) (PreH12 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> ((((Znth i_2 left_limits 0) = (fst ((fst ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth i_2 times 0) = (snd ((fst ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i_2 maxima 0) = (snd ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z))))))),
  (Int64Array.full_shape out_pre n_pre )
|--
  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < 0)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 (@nil Z) 0) )) ”
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000))) ”
  &&  (Int64Array.undef_seg out_pre 0 n_pre )
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (n_pre: Z) (out_pre: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((((1 <= (fst ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth i queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH8 : (n_pre = (Zlength (queries)))) (PreH9 : ((Zlength (left_limits)) = n_pre)) (PreH10 : ((Zlength (times)) = n_pre)) (PreH11 : ((Zlength (maxima)) = n_pre)) (PreH12 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> ((((Znth i_2 left_limits 0) = (fst ((fst ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth i_2 times 0) = (snd ((fst ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i_2 maxima 0) = (snd ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z))))))),
  (Int64Array.full_shape out_pre n_pre )
|--
  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < 0)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 (@nil Z) 0) )) ”
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (n_pre: Z) (out_pre: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((((1 <= (fst ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth i queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH8 : (n_pre = (Zlength (queries)))) (PreH9 : ((Zlength (left_limits)) = n_pre)) (PreH10 : ((Zlength (times)) = n_pre)) (PreH11 : ((Zlength (maxima)) = n_pre)) (PreH12 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> ((((Znth i_2 left_limits 0) = (fst ((fst ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth i_2 times 0) = (snd ((fst ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i_2 maxima 0) = (snd ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z))))))),
  (Int64Array.full_shape out_pre n_pre )
|--
  “ ((Zlength ((@nil Z))) = 0) ”
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (n_pre: Z) (out_pre: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((((1 <= (fst ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth i queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH8 : (n_pre = (Zlength (queries)))) (PreH9 : ((Zlength (left_limits)) = n_pre)) (PreH10 : ((Zlength (times)) = n_pre)) (PreH11 : ((Zlength (maxima)) = n_pre)) (PreH12 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> ((((Znth i_2 left_limits 0) = (fst ((fst ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth i_2 times 0) = (snd ((fst ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i_2 maxima 0) = (snd ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z))))))),
  (Int64Array.full_shape out_pre n_pre )
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) ”
.

Definition solver_entail_wit_1_split_goal_4 :=
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (n_pre: Z) (out_pre: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((((1 <= (fst ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth i queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH8 : (n_pre = (Zlength (queries)))) (PreH9 : ((Zlength (left_limits)) = n_pre)) (PreH10 : ((Zlength (times)) = n_pre)) (PreH11 : ((Zlength (maxima)) = n_pre)) (PreH12 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> ((((Znth i_2 left_limits 0) = (fst ((fst ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth i_2 times 0) = (snd ((fst ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i_2 maxima 0) = (snd ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z))))))),
  (Int64Array.full_shape out_pre n_pre )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000))) ”
.

Definition solver_entail_wit_1_split_goal_spatial :=
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (n_pre: Z) (out_pre: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (1 <= A_pre)) (PreH2 : (A_pre <= 1000000)) (PreH3 : (1 <= B_pre)) (PreH4 : (B_pre <= 1000000)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : forall (i: Z), (((0 <= i) /\ (i < n_pre)) -> ((((((1 <= (fst ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth i queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth i queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH8 : (n_pre = (Zlength (queries)))) (PreH9 : ((Zlength (left_limits)) = n_pre)) (PreH10 : ((Zlength (times)) = n_pre)) (PreH11 : ((Zlength (maxima)) = n_pre)) (PreH12 : forall (i_2: Z), (((0 <= i_2) /\ (i_2 < n_pre)) -> ((((Znth i_2 left_limits 0) = (fst ((fst ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth i_2 times 0) = (snd ((fst ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth i_2 maxima 0) = (snd ((Znth i_2 queries __default__Prod__Prod_Z_Z_Z))))))),
  (Int64Array.full_shape out_pre n_pre )
|--
  (Int64Array.undef_seg out_pre 0 n_pre )
.

Definition solver_entail_wit_2 :=
(
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (ql_pre: Z) (qt_pre: Z) (qm_pre: Z) (n_pre: Z) (out_pre: Z) (result_2: (@list Z)) (i: Z) (retval: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((-1) <= retval)) (PreH2 : (retval <= 2000000)) (PreH3 : (QueryAnswer A_pre B_pre (pair ((pair ((Znth i left_limits 0)) ((Znth i times 0)))) ((Znth i maxima 0))) retval )) (PreH4 : (i < n_pre)) (PreH5 : (1 <= A_pre)) (PreH6 : (A_pre <= 1000000)) (PreH7 : (1 <= B_pre)) (PreH8 : (B_pre <= 1000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000)) (PreH11 : (n_pre = (Zlength (queries)))) (PreH12 : ((Zlength (left_limits)) = n_pre)) (PreH13 : ((Zlength (times)) = n_pre)) (PreH14 : ((Zlength (maxima)) = n_pre)) (PreH15 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : ((Zlength (result_2)) = i)) (PreH20 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result_2 0) ))),
  (Int64Array.seg out_pre 0 (i + 1 ) (app (result_2) ((cons (retval) ((@nil Z))))) )
  **  (Int64Array.undef_seg out_pre (i + 1 ) n_pre )
  **  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full ql_pre n_pre left_limits )
|--
  EX (result: (@list Z)),
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (queries))) ”
  &&  “ ((Zlength (left_limits)) = n_pre) ”
  &&  “ ((Zlength (times)) = n_pre) ”
  &&  “ ((Zlength (maxima)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (result)) = (i + 1 )) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) )) ”
  &&  (Int64Array.full ql_pre n_pre left_limits )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.seg out_pre 0 (i + 1 ) result )
  **  (Int64Array.undef_seg out_pre (i + 1 ) n_pre )
) \/
(
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (n_pre: Z) (result_2: (@list Z)) (i: Z) (retval: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((-1) <= retval)) (PreH2 : (retval <= 2000000)) (PreH3 : (QueryAnswer A_pre B_pre (pair ((pair ((Znth i left_limits 0)) ((Znth i times 0)))) ((Znth i maxima 0))) retval )) (PreH4 : (i < n_pre)) (PreH5 : (1 <= A_pre)) (PreH6 : (A_pre <= 1000000)) (PreH7 : (1 <= B_pre)) (PreH8 : (B_pre <= 1000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000)) (PreH11 : (n_pre = (Zlength (queries)))) (PreH12 : ((Zlength (left_limits)) = n_pre)) (PreH13 : ((Zlength (times)) = n_pre)) (PreH14 : ((Zlength (maxima)) = n_pre)) (PreH15 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : ((Zlength (result_2)) = i)) (PreH20 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result_2 0) ))),
  TT && emp 
|--
  “ ((Zlength ((app (result_2) ((cons (retval) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 :=
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (n_pre: Z) (result_2: (@list Z)) (i: Z) (retval: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((-1) <= retval)) (PreH2 : (retval <= 2000000)) (PreH3 : (QueryAnswer A_pre B_pre (pair ((pair ((Znth i left_limits 0)) ((Znth i times 0)))) ((Znth i maxima 0))) retval )) (PreH4 : (i < n_pre)) (PreH5 : (1 <= A_pre)) (PreH6 : (A_pre <= 1000000)) (PreH7 : (1 <= B_pre)) (PreH8 : (B_pre <= 1000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000)) (PreH11 : (n_pre = (Zlength (queries)))) (PreH12 : ((Zlength (left_limits)) = n_pre)) (PreH13 : ((Zlength (times)) = n_pre)) (PreH14 : ((Zlength (maxima)) = n_pre)) (PreH15 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : ((Zlength (result_2)) = i)) (PreH20 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result_2 0) ))),
  ((Zlength ((app (result_2) ((cons (retval) ((@nil Z))))))) = (i + 1 ))
.

Definition solver_return_wit_1 :=
(
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (ql_pre: Z) (qt_pre: Z) (qm_pre: Z) (n_pre: Z) (out_pre: Z) (result_2: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (n_pre = (Zlength (queries)))) (PreH9 : ((Zlength (left_limits)) = n_pre)) (PreH10 : ((Zlength (times)) = n_pre)) (PreH11 : ((Zlength (maxima)) = n_pre)) (PreH12 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH13 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (result_2)) = i)) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result_2 0) ))),
  (Int64Array.full ql_pre n_pre left_limits )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.seg out_pre 0 i result_2 )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  EX (result: (@list Z)),
  “ (Spec A_pre B_pre queries result ) ”
  &&  (Int64Array.full ql_pre n_pre left_limits )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.full out_pre n_pre result )
) \/
(
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (n_pre: Z) (result_2: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (n_pre = (Zlength (queries)))) (PreH9 : ((Zlength (left_limits)) = n_pre)) (PreH10 : ((Zlength (times)) = n_pre)) (PreH11 : ((Zlength (maxima)) = n_pre)) (PreH12 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH13 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (result_2)) = i)) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result_2 0) ))),
  TT && emp 
|--
  “ (Spec A_pre B_pre queries result_2 ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (n_pre: Z) (result_2: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i >= n_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (n_pre = (Zlength (queries)))) (PreH9 : ((Zlength (left_limits)) = n_pre)) (PreH10 : ((Zlength (times)) = n_pre)) (PreH11 : ((Zlength (maxima)) = n_pre)) (PreH12 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH13 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (result_2)) = i)) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result_2 0) ))),
  (Spec A_pre B_pre queries result_2 )
.

Definition solver_partial_solve_wit_1 :=
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (ql_pre: Z) (qt_pre: Z) (qm_pre: Z) (n_pre: Z) (out_pre: Z) (result: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (n_pre = (Zlength (queries)))) (PreH9 : ((Zlength (left_limits)) = n_pre)) (PreH10 : ((Zlength (times)) = n_pre)) (PreH11 : ((Zlength (maxima)) = n_pre)) (PreH12 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH13 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (result)) = i)) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) ))),
  (Int64Array.full ql_pre n_pre left_limits )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (i < n_pre) ”
  &&  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (queries))) ”
  &&  “ ((Zlength (left_limits)) = n_pre) ”
  &&  “ ((Zlength (times)) = n_pre) ”
  &&  “ ((Zlength (maxima)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (result)) = i) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) )) ”
  &&  (((ql_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i left_limits 0))
  **  (Int64Array.missing_i ql_pre i 0 n_pre left_limits )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i n_pre )
.

Definition solver_partial_solve_wit_2 :=
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (ql_pre: Z) (qt_pre: Z) (qm_pre: Z) (n_pre: Z) (out_pre: Z) (result: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (n_pre = (Zlength (queries)))) (PreH9 : ((Zlength (left_limits)) = n_pre)) (PreH10 : ((Zlength (times)) = n_pre)) (PreH11 : ((Zlength (maxima)) = n_pre)) (PreH12 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH13 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (result)) = i)) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) ))),
  (Int64Array.full ql_pre n_pre left_limits )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (i < n_pre) ”
  &&  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (queries))) ”
  &&  “ ((Zlength (left_limits)) = n_pre) ”
  &&  “ ((Zlength (times)) = n_pre) ”
  &&  “ ((Zlength (maxima)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (result)) = i) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) )) ”
  &&  (((qt_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i times 0))
  **  (Int64Array.missing_i qt_pre i 0 n_pre times )
  **  (Int64Array.full ql_pre n_pre left_limits )
  **  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i n_pre )
.

Definition solver_partial_solve_wit_3 :=
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (ql_pre: Z) (qt_pre: Z) (qm_pre: Z) (n_pre: Z) (out_pre: Z) (result: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (n_pre = (Zlength (queries)))) (PreH9 : ((Zlength (left_limits)) = n_pre)) (PreH10 : ((Zlength (times)) = n_pre)) (PreH11 : ((Zlength (maxima)) = n_pre)) (PreH12 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH13 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (result)) = i)) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) ))),
  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full ql_pre n_pre left_limits )
  **  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (i < n_pre) ”
  &&  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (queries))) ”
  &&  “ ((Zlength (left_limits)) = n_pre) ”
  &&  “ ((Zlength (times)) = n_pre) ”
  &&  “ ((Zlength (maxima)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (result)) = i) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) )) ”
  &&  (((qm_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i maxima 0))
  **  (Int64Array.missing_i qm_pre i 0 n_pre maxima )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full ql_pre n_pre left_limits )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i n_pre )
.

Definition solver_partial_solve_wit_4_pure :=
(
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (ql_pre: Z) (qt_pre: Z) (qm_pre: Z) (n_pre: Z) (out_pre: Z) (result: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (n_pre = (Zlength (queries)))) (PreH9 : ((Zlength (left_limits)) = n_pre)) (PreH10 : ((Zlength (times)) = n_pre)) (PreH11 : ((Zlength (maxima)) = n_pre)) (PreH12 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH13 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (result)) = i)) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) ))),
  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full ql_pre n_pre left_limits )
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "ql" ) )) # Ptr  |-> ql_pre)
  **  ((( &( "qt" ) )) # Ptr  |-> qt_pre)
  **  ((( &( "qm" ) )) # Ptr  |-> qm_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ ((Znth i maxima 0) <= 1000000) ”
  &&  “ (1 <= (Znth i maxima 0)) ”
  &&  “ ((Znth i times 0) <= 1000000) ”
  &&  “ (1 <= (Znth i times 0)) ”
  &&  “ ((Znth i left_limits 0) <= 1000000) ”
  &&  “ (1 <= (Znth i left_limits 0)) ”
) \/
(
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (ql_pre: Z) (qt_pre: Z) (qm_pre: Z) (n_pre: Z) (out_pre: Z) (result: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (B_pre <= INT64_MAX)) (PreH2 : (A_pre <= INT64_MAX)) (PreH3 : (B_pre >= INT64_MIN)) (PreH4 : (A_pre >= INT64_MIN)) (PreH5 : (i <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < n_pre)) (PreH10 : (1 <= A_pre)) (PreH11 : (A_pre <= 1000000)) (PreH12 : (1 <= B_pre)) (PreH13 : (B_pre <= 1000000)) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : (n_pre = (Zlength (queries)))) (PreH17 : ((Zlength (left_limits)) = n_pre)) (PreH18 : ((Zlength (times)) = n_pre)) (PreH19 : ((Zlength (maxima)) = n_pre)) (PreH20 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH21 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : ((Zlength (result)) = i)) (PreH25 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) ))),
  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full ql_pre n_pre left_limits )
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "ql" ) )) # Ptr  |-> ql_pre)
  **  ((( &( "qt" ) )) # Ptr  |-> qt_pre)
  **  ((( &( "qm" ) )) # Ptr  |-> qm_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (1 <= (Znth i left_limits 0)) ”
  &&  “ ((Znth i left_limits 0) <= 1000000) ”
  &&  “ (1 <= (Znth i times 0)) ”
  &&  “ ((Znth i times 0) <= 1000000) ”
  &&  “ (1 <= (Znth i maxima 0)) ”
  &&  “ ((Znth i maxima 0) <= 1000000) ”
).

Definition solver_partial_solve_wit_4_pure_split_goal_1 :=
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (ql_pre: Z) (qt_pre: Z) (qm_pre: Z) (n_pre: Z) (out_pre: Z) (result: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (B_pre <= INT64_MAX)) (PreH2 : (A_pre <= INT64_MAX)) (PreH3 : (B_pre >= INT64_MIN)) (PreH4 : (A_pre >= INT64_MIN)) (PreH5 : (i <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < n_pre)) (PreH10 : (1 <= A_pre)) (PreH11 : (A_pre <= 1000000)) (PreH12 : (1 <= B_pre)) (PreH13 : (B_pre <= 1000000)) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : (n_pre = (Zlength (queries)))) (PreH17 : ((Zlength (left_limits)) = n_pre)) (PreH18 : ((Zlength (times)) = n_pre)) (PreH19 : ((Zlength (maxima)) = n_pre)) (PreH20 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH21 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : ((Zlength (result)) = i)) (PreH25 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) ))),
  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full ql_pre n_pre left_limits )
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "ql" ) )) # Ptr  |-> ql_pre)
  **  ((( &( "qt" ) )) # Ptr  |-> qt_pre)
  **  ((( &( "qm" ) )) # Ptr  |-> qm_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (1 <= (Znth i left_limits 0)) ”
.

Definition solver_partial_solve_wit_4_pure_split_goal_2 :=
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (ql_pre: Z) (qt_pre: Z) (qm_pre: Z) (n_pre: Z) (out_pre: Z) (result: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (B_pre <= INT64_MAX)) (PreH2 : (A_pre <= INT64_MAX)) (PreH3 : (B_pre >= INT64_MIN)) (PreH4 : (A_pre >= INT64_MIN)) (PreH5 : (i <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < n_pre)) (PreH10 : (1 <= A_pre)) (PreH11 : (A_pre <= 1000000)) (PreH12 : (1 <= B_pre)) (PreH13 : (B_pre <= 1000000)) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : (n_pre = (Zlength (queries)))) (PreH17 : ((Zlength (left_limits)) = n_pre)) (PreH18 : ((Zlength (times)) = n_pre)) (PreH19 : ((Zlength (maxima)) = n_pre)) (PreH20 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH21 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : ((Zlength (result)) = i)) (PreH25 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) ))),
  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full ql_pre n_pre left_limits )
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "ql" ) )) # Ptr  |-> ql_pre)
  **  ((( &( "qt" ) )) # Ptr  |-> qt_pre)
  **  ((( &( "qm" ) )) # Ptr  |-> qm_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ ((Znth i left_limits 0) <= 1000000) ”
.

Definition solver_partial_solve_wit_4_pure_split_goal_3 :=
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (ql_pre: Z) (qt_pre: Z) (qm_pre: Z) (n_pre: Z) (out_pre: Z) (result: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (B_pre <= INT64_MAX)) (PreH2 : (A_pre <= INT64_MAX)) (PreH3 : (B_pre >= INT64_MIN)) (PreH4 : (A_pre >= INT64_MIN)) (PreH5 : (i <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < n_pre)) (PreH10 : (1 <= A_pre)) (PreH11 : (A_pre <= 1000000)) (PreH12 : (1 <= B_pre)) (PreH13 : (B_pre <= 1000000)) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : (n_pre = (Zlength (queries)))) (PreH17 : ((Zlength (left_limits)) = n_pre)) (PreH18 : ((Zlength (times)) = n_pre)) (PreH19 : ((Zlength (maxima)) = n_pre)) (PreH20 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH21 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : ((Zlength (result)) = i)) (PreH25 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) ))),
  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full ql_pre n_pre left_limits )
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "ql" ) )) # Ptr  |-> ql_pre)
  **  ((( &( "qt" ) )) # Ptr  |-> qt_pre)
  **  ((( &( "qm" ) )) # Ptr  |-> qm_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (1 <= (Znth i times 0)) ”
.

Definition solver_partial_solve_wit_4_pure_split_goal_4 :=
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (ql_pre: Z) (qt_pre: Z) (qm_pre: Z) (n_pre: Z) (out_pre: Z) (result: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (B_pre <= INT64_MAX)) (PreH2 : (A_pre <= INT64_MAX)) (PreH3 : (B_pre >= INT64_MIN)) (PreH4 : (A_pre >= INT64_MIN)) (PreH5 : (i <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < n_pre)) (PreH10 : (1 <= A_pre)) (PreH11 : (A_pre <= 1000000)) (PreH12 : (1 <= B_pre)) (PreH13 : (B_pre <= 1000000)) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : (n_pre = (Zlength (queries)))) (PreH17 : ((Zlength (left_limits)) = n_pre)) (PreH18 : ((Zlength (times)) = n_pre)) (PreH19 : ((Zlength (maxima)) = n_pre)) (PreH20 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH21 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : ((Zlength (result)) = i)) (PreH25 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) ))),
  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full ql_pre n_pre left_limits )
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "ql" ) )) # Ptr  |-> ql_pre)
  **  ((( &( "qt" ) )) # Ptr  |-> qt_pre)
  **  ((( &( "qm" ) )) # Ptr  |-> qm_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ ((Znth i times 0) <= 1000000) ”
.

Definition solver_partial_solve_wit_4_pure_split_goal_5 :=
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (ql_pre: Z) (qt_pre: Z) (qm_pre: Z) (n_pre: Z) (out_pre: Z) (result: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (B_pre <= INT64_MAX)) (PreH2 : (A_pre <= INT64_MAX)) (PreH3 : (B_pre >= INT64_MIN)) (PreH4 : (A_pre >= INT64_MIN)) (PreH5 : (i <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < n_pre)) (PreH10 : (1 <= A_pre)) (PreH11 : (A_pre <= 1000000)) (PreH12 : (1 <= B_pre)) (PreH13 : (B_pre <= 1000000)) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : (n_pre = (Zlength (queries)))) (PreH17 : ((Zlength (left_limits)) = n_pre)) (PreH18 : ((Zlength (times)) = n_pre)) (PreH19 : ((Zlength (maxima)) = n_pre)) (PreH20 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH21 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : ((Zlength (result)) = i)) (PreH25 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) ))),
  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full ql_pre n_pre left_limits )
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "ql" ) )) # Ptr  |-> ql_pre)
  **  ((( &( "qt" ) )) # Ptr  |-> qt_pre)
  **  ((( &( "qm" ) )) # Ptr  |-> qm_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (1 <= (Znth i maxima 0)) ”
.

Definition solver_partial_solve_wit_4_pure_split_goal_6 :=
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (ql_pre: Z) (qt_pre: Z) (qm_pre: Z) (n_pre: Z) (out_pre: Z) (result: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (B_pre <= INT64_MAX)) (PreH2 : (A_pre <= INT64_MAX)) (PreH3 : (B_pre >= INT64_MIN)) (PreH4 : (A_pre >= INT64_MIN)) (PreH5 : (i <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i < n_pre)) (PreH10 : (1 <= A_pre)) (PreH11 : (A_pre <= 1000000)) (PreH12 : (1 <= B_pre)) (PreH13 : (B_pre <= 1000000)) (PreH14 : (1 <= n_pre)) (PreH15 : (n_pre <= 100000)) (PreH16 : (n_pre = (Zlength (queries)))) (PreH17 : ((Zlength (left_limits)) = n_pre)) (PreH18 : ((Zlength (times)) = n_pre)) (PreH19 : ((Zlength (maxima)) = n_pre)) (PreH20 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH21 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : ((Zlength (result)) = i)) (PreH25 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) ))),
  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full ql_pre n_pre left_limits )
  **  ((( &( "A" ) )) # Int64  |-> A_pre)
  **  ((( &( "B" ) )) # Int64  |-> B_pre)
  **  ((( &( "ql" ) )) # Ptr  |-> ql_pre)
  **  ((( &( "qt" ) )) # Ptr  |-> qt_pre)
  **  ((( &( "qm" ) )) # Ptr  |-> qm_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ ((Znth i maxima 0) <= 1000000) ”
.

Definition solver_partial_solve_wit_4_aux :=
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (ql_pre: Z) (qt_pre: Z) (qm_pre: Z) (n_pre: Z) (out_pre: Z) (result: (@list Z)) (i: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : (i < n_pre)) (PreH2 : (1 <= A_pre)) (PreH3 : (A_pre <= 1000000)) (PreH4 : (1 <= B_pre)) (PreH5 : (B_pre <= 1000000)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100000)) (PreH8 : (n_pre = (Zlength (queries)))) (PreH9 : ((Zlength (left_limits)) = n_pre)) (PreH10 : ((Zlength (times)) = n_pre)) (PreH11 : ((Zlength (maxima)) = n_pre)) (PreH12 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH13 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((Zlength (result)) = i)) (PreH17 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) ))),
  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full ql_pre n_pre left_limits )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ ((Znth i maxima 0) <= 1000000) ”
  &&  “ (1 <= (Znth i maxima 0)) ”
  &&  “ ((Znth i times 0) <= 1000000) ”
  &&  “ (1 <= (Znth i times 0)) ”
  &&  “ ((Znth i left_limits 0) <= 1000000) ”
  &&  “ (1 <= (Znth i left_limits 0)) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (queries))) ”
  &&  “ ((Zlength (left_limits)) = n_pre) ”
  &&  “ ((Zlength (times)) = n_pre) ”
  &&  “ ((Zlength (maxima)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (result)) = i) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) )) ”
  &&  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full ql_pre n_pre left_limits )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i n_pre )
.

Definition solver_partial_solve_wit_4 := solver_partial_solve_wit_4_pure -> solver_partial_solve_wit_4_aux.

Definition solver_partial_solve_wit_5 :=
forall (maxima: (@list Z)) (times: (@list Z)) (left_limits: (@list Z)) (queries: (@list ((Z * Z) * Z))) (A_pre: Z) (B_pre: Z) (ql_pre: Z) (qt_pre: Z) (qm_pre: Z) (n_pre: Z) (out_pre: Z) (result: (@list Z)) (i: Z) (retval: Z) __default__Prod__Prod_Z_Z_Z (PreH1 : ((-1) <= retval)) (PreH2 : (retval <= 2000000)) (PreH3 : (QueryAnswer A_pre B_pre (pair ((pair ((Znth i left_limits 0)) ((Znth i times 0)))) ((Znth i maxima 0))) retval )) (PreH4 : (i < n_pre)) (PreH5 : (1 <= A_pre)) (PreH6 : (A_pre <= 1000000)) (PreH7 : (1 <= B_pre)) (PreH8 : (B_pre <= 1000000)) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 100000)) (PreH11 : (n_pre = (Zlength (queries)))) (PreH12 : ((Zlength (left_limits)) = n_pre)) (PreH13 : ((Zlength (times)) = n_pre)) (PreH14 : ((Zlength (maxima)) = n_pre)) (PreH15 : forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000)))) (PreH16 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : ((Zlength (result)) = i)) (PreH20 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) ))),
  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full ql_pre n_pre left_limits )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i n_pre )
|--
  “ ((-1) <= retval) ”
  &&  “ (retval <= 2000000) ”
  &&  “ (QueryAnswer A_pre B_pre (pair ((pair ((Znth i left_limits 0)) ((Znth i times 0)))) ((Znth i maxima 0))) retval ) ”
  &&  “ (i < n_pre) ”
  &&  “ (1 <= A_pre) ”
  &&  “ (A_pre <= 1000000) ”
  &&  “ (1 <= B_pre) ”
  &&  “ (B_pre <= 1000000) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 100000) ”
  &&  “ (n_pre = (Zlength (queries))) ”
  &&  “ ((Zlength (left_limits)) = n_pre) ”
  &&  “ ((Zlength (times)) = n_pre) ”
  &&  “ ((Zlength (maxima)) = n_pre) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < n_pre)) -> ((((((1 <= (fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((fst ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((snd ((fst ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) <= 1000000)) /\ (1 <= (snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))))) /\ ((snd ((Znth k queries __default__Prod__Prod_Z_Z_Z))) <= 1000000))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((Znth k_2 left_limits 0) = (fst ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) /\ ((Znth k_2 times 0) = (snd ((fst ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z))))))) /\ ((Znth k_2 maxima 0) = (snd ((Znth k_2 queries __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (result)) = i) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < i)) -> (QueryAnswer A_pre B_pre (Znth k_3 queries __default__Prod__Prod_Z_Z_Z) (Znth k_3 result 0) )) ”
  &&  (((out_pre + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg out_pre (i + 1 ) n_pre )
  **  (Int64Array.full qm_pre n_pre maxima )
  **  (Int64Array.full qt_pre n_pre times )
  **  (Int64Array.full ql_pre n_pre left_limits )
  **  (Int64Array.seg out_pre 0 i result )
.

Module Type VC_Correct.


Axiom proof_of_height_safety_wit_1 : height_safety_wit_1.
Axiom proof_of_height_safety_wit_2 : height_safety_wit_2.
Axiom proof_of_height_safety_wit_3 : height_safety_wit_3.
Axiom proof_of_height_safety_wit_4 : height_safety_wit_4.
Axiom proof_of_height_return_wit_1 : height_return_wit_1.
Axiom proof_of_range_sum_safety_wit_1 : range_sum_safety_wit_1.
Axiom proof_of_range_sum_safety_wit_2 : range_sum_safety_wit_2.
Axiom proof_of_range_sum_safety_wit_3 : range_sum_safety_wit_3.
Axiom proof_of_range_sum_safety_wit_4 : range_sum_safety_wit_4.
Axiom proof_of_range_sum_safety_wit_5 : range_sum_safety_wit_5.
Axiom proof_of_range_sum_safety_wit_6 : range_sum_safety_wit_6.
Axiom proof_of_range_sum_safety_wit_7 : range_sum_safety_wit_7.
Axiom proof_of_range_sum_return_wit_1 : range_sum_return_wit_1.
Axiom proof_of_range_sum_partial_solve_wit_1_pure : range_sum_partial_solve_wit_1_pure.
Axiom proof_of_range_sum_partial_solve_wit_1 : range_sum_partial_solve_wit_1.
Axiom proof_of_range_sum_partial_solve_wit_2_pure : range_sum_partial_solve_wit_2_pure.
Axiom proof_of_range_sum_partial_solve_wit_2 : range_sum_partial_solve_wit_2.
Axiom proof_of_answer_query_safety_wit_1 : answer_query_safety_wit_1.
Axiom proof_of_answer_query_safety_wit_2 : answer_query_safety_wit_2.
Axiom proof_of_answer_query_safety_wit_3 : answer_query_safety_wit_3.
Axiom proof_of_answer_query_safety_wit_4 : answer_query_safety_wit_4.
Axiom proof_of_answer_query_safety_wit_5 : answer_query_safety_wit_5.
Axiom proof_of_answer_query_safety_wit_6 : answer_query_safety_wit_6.
Axiom proof_of_answer_query_safety_wit_7 : answer_query_safety_wit_7.
Axiom proof_of_answer_query_safety_wit_8 : answer_query_safety_wit_8.
Axiom proof_of_answer_query_safety_wit_9 : answer_query_safety_wit_9.
Axiom proof_of_answer_query_safety_wit_10 : answer_query_safety_wit_10.
Axiom proof_of_answer_query_safety_wit_11 : answer_query_safety_wit_11.
Axiom proof_of_answer_query_safety_wit_12 : answer_query_safety_wit_12.
Axiom proof_of_answer_query_safety_wit_13 : answer_query_safety_wit_13.
Axiom proof_of_answer_query_safety_wit_14 : answer_query_safety_wit_14.
Axiom proof_of_answer_query_safety_wit_15 : answer_query_safety_wit_15.
Axiom proof_of_answer_query_entail_wit_1 : answer_query_entail_wit_1.
Axiom proof_of_answer_query_entail_wit_2 : answer_query_entail_wit_2.
Axiom proof_of_answer_query_entail_wit_3 : answer_query_entail_wit_3.
Axiom proof_of_answer_query_entail_wit_4 : answer_query_entail_wit_4.
Axiom proof_of_answer_query_entail_wit_5_1 : answer_query_entail_wit_5_1.
Axiom proof_of_answer_query_entail_wit_5_2 : answer_query_entail_wit_5_2.
Axiom proof_of_answer_query_entail_wit_5_3 : answer_query_entail_wit_5_3.
Axiom proof_of_answer_query_return_wit_1 : answer_query_return_wit_1.
Axiom proof_of_answer_query_return_wit_2 : answer_query_return_wit_2.
Axiom proof_of_answer_query_partial_solve_wit_1_pure : answer_query_partial_solve_wit_1_pure.
Axiom proof_of_answer_query_partial_solve_wit_1 : answer_query_partial_solve_wit_1.
Axiom proof_of_answer_query_partial_solve_wit_2_pure : answer_query_partial_solve_wit_2_pure.
Axiom proof_of_answer_query_partial_solve_wit_2 : answer_query_partial_solve_wit_2.
Axiom proof_of_answer_query_partial_solve_wit_3_pure : answer_query_partial_solve_wit_3_pure.
Axiom proof_of_answer_query_partial_solve_wit_3 : answer_query_partial_solve_wit_3.
Axiom proof_of_answer_query_partial_solve_wit_4_pure : answer_query_partial_solve_wit_4_pure.
Axiom proof_of_answer_query_partial_solve_wit_4 : answer_query_partial_solve_wit_4.
Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.

End VC_Correct.
