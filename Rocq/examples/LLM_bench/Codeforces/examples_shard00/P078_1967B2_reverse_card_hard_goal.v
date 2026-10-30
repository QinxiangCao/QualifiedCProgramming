From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P078_1967B2_reverse_card_hard_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P078_1967B2_reverse_card_hard_lib.
Local Open Scope sac.

(*----- Function gcd_int -----*)

Definition gcd_int_safety_wit_1 :=
forall (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (0 <= a)) (PreH2 : (a <= 2000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 2000000)) (PreH5 : ((RCgcd (a) (b)) = (RCgcd (a_pre) (b_pre)))) (PreH6 : (b <> 0)),
  ((( &( "t" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
|--
  “ ((a <> (INT_MIN)) \/ (b <> (-1))) ”
  &&  “ (b <> 0) ”
.

Definition gcd_int_entail_wit_1 :=
forall (a_pre: Z) (b_pre: Z) (PreH1 : (1 <= a_pre)) (PreH2 : (a_pre <= 2000000)) (PreH3 : (1 <= b_pre)) (PreH4 : (b_pre <= 2000000)),
  TT && emp 
|--
  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 2000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 2000000) ”
  &&  “ ((RCgcd (a_pre) (b_pre)) = (RCgcd (a_pre) (b_pre))) ”
  &&  emp
.

Definition gcd_int_entail_wit_2 :=
(
forall (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (0 <= a)) (PreH2 : (a <= 2000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 2000000)) (PreH5 : ((RCgcd (a) (b)) = (RCgcd (a_pre) (b_pre)))) (PreH6 : (b <> 0)),
  TT && emp 
|--
  “ (0 <= b) ”
  &&  “ (b <= 2000000) ”
  &&  “ (0 <= (a % ( b ) )) ”
  &&  “ ((a % ( b ) ) <= 2000000) ”
  &&  “ ((RCgcd (b) ((a % ( b ) ))) = (RCgcd (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (0 <= a)) (PreH2 : (a <= 2000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 2000000)) (PreH5 : ((RCgcd (a) (b)) = (RCgcd (a_pre) (b_pre)))) (PreH6 : (b <> 0)),
  TT && emp 
|--
  “ ((RCgcd (b) ((a % ( b ) ))) = (RCgcd (a_pre) (b_pre))) ”
  &&  “ ((a % ( b ) ) <= 2000000) ”
  &&  “ (0 <= (a % ( b ) )) ”
  &&  emp
).

Definition gcd_int_entail_wit_2_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (0 <= a)) (PreH2 : (a <= 2000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 2000000)) (PreH5 : ((RCgcd (a) (b)) = (RCgcd (a_pre) (b_pre)))) (PreH6 : (b <> 0)),
  ((RCgcd (b) ((a % ( b ) ))) = (RCgcd (a_pre) (b_pre)))
.

Definition gcd_int_entail_wit_2_split_goal_2 :=
forall (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (0 <= a)) (PreH2 : (a <= 2000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 2000000)) (PreH5 : ((RCgcd (a) (b)) = (RCgcd (a_pre) (b_pre)))) (PreH6 : (b <> 0)),
  ((a % ( b ) ) <= 2000000)
.

Definition gcd_int_entail_wit_2_split_goal_3 :=
forall (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (0 <= a)) (PreH2 : (a <= 2000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 2000000)) (PreH5 : ((RCgcd (a) (b)) = (RCgcd (a_pre) (b_pre)))) (PreH6 : (b <> 0)),
  (0 <= (a % ( b ) ))
.

Definition gcd_int_return_wit_1 :=
(
forall (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (0 <= a)) (PreH2 : (a <= 2000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 2000000)) (PreH5 : ((RCgcd (a) (b)) = (RCgcd (a_pre) (b_pre)))) (PreH6 : (b = 0)),
  TT && emp 
|--
  “ (a = (RCgcd (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (0 <= a)) (PreH2 : (a <= 2000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 2000000)) (PreH5 : ((RCgcd (a) (b)) = (RCgcd (a_pre) (b_pre)))) (PreH6 : (b = 0)),
  TT && emp 
|--
  “ (a = (RCgcd (a_pre) (b_pre))) ”
  &&  emp
).

Definition gcd_int_return_wit_1_split_goal_1 :=
forall (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (0 <= a)) (PreH2 : (a <= 2000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 2000000)) (PreH5 : ((RCgcd (a) (b)) = (RCgcd (a_pre) (b_pre)))) (PreH6 : (b = 0)),
  (a = (RCgcd (a_pre) (b_pre)))
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (n_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 2000000)),
  ((( &( "ans" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (n_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 2000000)),
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int64  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_3 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (p: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 2000000)) (PreH5 : (1 <= p)) (PreH6 : (p <= 1415)) (PreH7 : (0 <= ans)) (PreH8 : (ans <= (2000000 * ((p - 1 ) * 1415 ) ))) (PreH9 : (RCProgress n_pre m_pre p 1 ans )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ ((p * p ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (p * p )) ”
.

Definition solver_safety_wit_4 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (p: Z) (PreH1 : ((p * p ) < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 2000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 2000000)) (PreH6 : (1 <= p)) (PreH7 : (p <= 1415)) (PreH8 : (0 <= ans)) (PreH9 : (ans <= (2000000 * ((p - 1 ) * 1415 ) ))) (PreH10 : (RCProgress n_pre m_pre p 1 ans )),
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 2000000)) (PreH5 : (1 <= p)) (PreH6 : (p <= 1415)) (PreH7 : ((p * p ) < n_pre)) (PreH8 : (1 <= q)) (PreH9 : (q <= 1415)) (PreH10 : (0 <= ans)) (PreH11 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH12 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ ((q * q ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (q * q )) ”
.

Definition solver_safety_wit_6 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : (retval = (RCgcd (p) (q)))) (PreH2 : ((q * q ) < m_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 2000000)) (PreH7 : (1 <= p)) (PreH8 : (p <= 1415)) (PreH9 : ((p * p ) < n_pre)) (PreH10 : (1 <= q)) (PreH11 : (q <= 1415)) (PreH12 : (0 <= ans)) (PreH13 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH14 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_7 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) < (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "lim" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ ((n_pre <> (INT_MIN)) \/ (p <> (-1))) ”
  &&  “ (p <> 0) ”
.

Definition solver_safety_wit_8 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = (RCgcd (p) (q)))) (PreH3 : ((q * q ) < m_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 2000000)) (PreH8 : (1 <= p)) (PreH9 : (p <= 1415)) (PreH10 : ((p * p ) < n_pre)) (PreH11 : (1 <= q)) (PreH12 : (q <= 1415)) (PreH13 : (0 <= ans)) (PreH14 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH15 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "lim" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ ((m_pre <> (INT_MIN)) \/ (q <> (-1))) ”
  &&  “ (q <> 0) ”
.

Definition solver_safety_wit_9 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = (RCgcd (p) (q)))) (PreH3 : ((q * q ) < m_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 2000000)) (PreH8 : (1 <= p)) (PreH9 : (p <= 1415)) (PreH10 : ((p * p ) < n_pre)) (PreH11 : (1 <= q)) (PreH12 : (q <= 1415)) (PreH13 : (0 <= ans)) (PreH14 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH15 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "lim" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ ((n_pre <> (INT_MIN)) \/ (p <> (-1))) ”
  &&  “ (p <> 0) ”
.

Definition solver_safety_wit_10 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) >= (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "lim" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ ((m_pre <> (INT_MIN)) \/ (q <> (-1))) ”
  &&  “ (q <> 0) ”
.

Definition solver_safety_wit_11 :=
(
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) < (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "lim" ) )) # Int  |-> (n_pre ÷ p ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ ((ans + ((n_pre ÷ p ) ÷ (p + q ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (ans + ((n_pre ÷ p ) ÷ (p + q ) ) )) ”
) \/
(
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) < (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "lim" ) )) # Int  |-> (n_pre ÷ p ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ ((ans + ((n_pre ÷ p ) ÷ (p + q ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (ans + ((n_pre ÷ p ) ÷ (p + q ) ) )) ”
).

Definition solver_safety_wit_11_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) < (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "lim" ) )) # Int  |-> (n_pre ÷ p ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ ((ans + ((n_pre ÷ p ) ÷ (p + q ) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_11_split_goal_2 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) < (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "lim" ) )) # Int  |-> (n_pre ÷ p ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ ((INT64_MIN) <= (ans + ((n_pre ÷ p ) ÷ (p + q ) ) )) ”
.

Definition solver_safety_wit_12 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) < (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "lim" ) )) # Int  |-> (n_pre ÷ p ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ (((n_pre ÷ p ) <> (INT_MIN)) \/ ((p + q ) <> (-1))) ”
  &&  “ ((p + q ) <> 0) ”
.

Definition solver_safety_wit_13 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) < (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "lim" ) )) # Int  |-> (n_pre ÷ p ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ ((p + q ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (p + q )) ”
.

Definition solver_safety_wit_14 :=
(
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) >= (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "lim" ) )) # Int  |-> (m_pre ÷ q ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ ((ans + ((m_pre ÷ q ) ÷ (p + q ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (ans + ((m_pre ÷ q ) ÷ (p + q ) ) )) ”
) \/
(
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) >= (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "lim" ) )) # Int  |-> (m_pre ÷ q ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ ((ans + ((m_pre ÷ q ) ÷ (p + q ) ) ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (ans + ((m_pre ÷ q ) ÷ (p + q ) ) )) ”
).

Definition solver_safety_wit_14_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) >= (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "lim" ) )) # Int  |-> (m_pre ÷ q ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ ((ans + ((m_pre ÷ q ) ÷ (p + q ) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_14_split_goal_2 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) >= (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "lim" ) )) # Int  |-> (m_pre ÷ q ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ ((INT64_MIN) <= (ans + ((m_pre ÷ q ) ÷ (p + q ) ) )) ”
.

Definition solver_safety_wit_15 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) >= (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "lim" ) )) # Int  |-> (m_pre ÷ q ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ (((m_pre ÷ q ) <> (INT_MIN)) \/ ((p + q ) <> (-1))) ”
  &&  “ ((p + q ) <> 0) ”
.

Definition solver_safety_wit_16 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) >= (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "lim" ) )) # Int  |-> (m_pre ÷ q ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ ((p + q ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (p + q )) ”
.

Definition solver_safety_wit_17 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (PreH1 : ((q * q ) >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 2000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 2000000)) (PreH6 : (1 <= p)) (PreH7 : (p <= 1415)) (PreH8 : ((p * p ) < n_pre)) (PreH9 : (1 <= q)) (PreH10 : (q <= 1415)) (PreH11 : (0 <= ans)) (PreH12 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH13 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ ((p + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (p + 1 )) ”
.

Definition solver_safety_wit_18 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) < (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> (ans + ((n_pre ÷ p ) ÷ (p + q ) ) ))
|--
  “ ((q + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (q + 1 )) ”
.

Definition solver_safety_wit_19 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) >= (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> (ans + ((m_pre ÷ q ) ÷ (p + q ) ) ))
|--
  “ ((q + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (q + 1 )) ”
.

Definition solver_safety_wit_20 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (retval = (RCgcd (p) (q)))) (PreH3 : ((q * q ) < m_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 2000000)) (PreH8 : (1 <= p)) (PreH9 : (p <= 1415)) (PreH10 : ((p * p ) < n_pre)) (PreH11 : (1 <= q)) (PreH12 : (q <= 1415)) (PreH13 : (0 <= ans)) (PreH14 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH15 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ ((q + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (q + 1 )) ”
.

Definition solver_entail_wit_1 :=
(
forall (n_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 2000000)),
  TT && emp 
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 2000000) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= 1415) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (2000000 * ((1 - 1 ) * 1415 ) )) ”
  &&  “ (RCProgress n_pre m_pre 1 1 0 ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 2000000)),
  TT && emp 
|--
  “ (RCProgress n_pre m_pre 1 1 0 ) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 2000000)),
  (RCProgress n_pre m_pre 1 1 0 )
.

Definition solver_entail_wit_2 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (p: Z) (PreH1 : ((p * p ) < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 2000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 2000000)) (PreH6 : (1 <= p)) (PreH7 : (p <= 1415)) (PreH8 : (0 <= ans)) (PreH9 : (ans <= (2000000 * ((p - 1 ) * 1415 ) ))) (PreH10 : (RCProgress n_pre m_pre p 1 ans )),
  TT && emp 
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 2000000) ”
  &&  “ (1 <= p) ”
  &&  “ (p <= 1415) ”
  &&  “ ((p * p ) < n_pre) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= 1415) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= (2000000 * (((p - 1 ) * 1415 ) + (1 - 1 ) ) )) ”
  &&  “ (RCProgress n_pre m_pre p 1 ans ) ”
  &&  emp
.

Definition solver_entail_wit_3 :=
(
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (PreH1 : ((q * q ) >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 2000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 2000000)) (PreH6 : (1 <= p)) (PreH7 : (p <= 1415)) (PreH8 : ((p * p ) < n_pre)) (PreH9 : (1 <= q)) (PreH10 : (q <= 1415)) (PreH11 : (0 <= ans)) (PreH12 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH13 : (RCProgress n_pre m_pre p q ans )),
  TT && emp 
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 2000000) ”
  &&  “ (1 <= (p + 1 )) ”
  &&  “ ((p + 1 ) <= 1415) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= (2000000 * (((p + 1 ) - 1 ) * 1415 ) )) ”
  &&  “ (RCProgress n_pre m_pre (p + 1 ) 1 ans ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (PreH1 : ((q * q ) >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 2000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 2000000)) (PreH6 : (1 <= p)) (PreH7 : (p <= 1415)) (PreH8 : ((p * p ) < n_pre)) (PreH9 : (1 <= q)) (PreH10 : (q <= 1415)) (PreH11 : (0 <= ans)) (PreH12 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH13 : (RCProgress n_pre m_pre p q ans )),
  TT && emp 
|--
  “ (RCProgress n_pre m_pre (p + 1 ) 1 ans ) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (PreH1 : ((q * q ) >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 2000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 2000000)) (PreH6 : (1 <= p)) (PreH7 : (p <= 1415)) (PreH8 : ((p * p ) < n_pre)) (PreH9 : (1 <= q)) (PreH10 : (q <= 1415)) (PreH11 : (0 <= ans)) (PreH12 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH13 : (RCProgress n_pre m_pre p q ans )),
  (RCProgress n_pre m_pre (p + 1 ) 1 ans )
.

Definition solver_entail_wit_4_1 :=
(
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) < (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  TT && emp 
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 2000000) ”
  &&  “ (1 <= p) ”
  &&  “ (p <= 1415) ”
  &&  “ ((p * p ) < n_pre) ”
  &&  “ (1 <= (q + 1 )) ”
  &&  “ ((q + 1 ) <= 1415) ”
  &&  “ (0 <= (ans + ((n_pre ÷ p ) ÷ (p + q ) ) )) ”
  &&  “ ((ans + ((n_pre ÷ p ) ÷ (p + q ) ) ) <= (2000000 * (((p - 1 ) * 1415 ) + ((q + 1 ) - 1 ) ) )) ”
  &&  “ (RCProgress n_pre m_pre p (q + 1 ) (ans + ((n_pre ÷ p ) ÷ (p + q ) ) ) ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) < (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  TT && emp 
|--
  “ (RCProgress n_pre m_pre p (q + 1 ) (ans + ((n_pre ÷ p ) ÷ (p + q ) ) ) ) ”
  &&  “ ((ans + ((n_pre ÷ p ) ÷ (p + q ) ) ) <= (2000000 * (((p - 1 ) * 1415 ) + ((q + 1 ) - 1 ) ) )) ”
  &&  “ (0 <= (ans + ((n_pre ÷ p ) ÷ (p + q ) ) )) ”
  &&  emp
).

Definition solver_entail_wit_4_1_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) < (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  (RCProgress n_pre m_pre p (q + 1 ) (ans + ((n_pre ÷ p ) ÷ (p + q ) ) ) )
.

Definition solver_entail_wit_4_1_split_goal_2 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) < (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  ((ans + ((n_pre ÷ p ) ÷ (p + q ) ) ) <= (2000000 * (((p - 1 ) * 1415 ) + ((q + 1 ) - 1 ) ) ))
.

Definition solver_entail_wit_4_1_split_goal_3 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) < (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  (0 <= (ans + ((n_pre ÷ p ) ÷ (p + q ) ) ))
.

Definition solver_entail_wit_4_2 :=
(
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) >= (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  TT && emp 
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 2000000) ”
  &&  “ (1 <= p) ”
  &&  “ (p <= 1415) ”
  &&  “ ((p * p ) < n_pre) ”
  &&  “ (1 <= (q + 1 )) ”
  &&  “ ((q + 1 ) <= 1415) ”
  &&  “ (0 <= (ans + ((m_pre ÷ q ) ÷ (p + q ) ) )) ”
  &&  “ ((ans + ((m_pre ÷ q ) ÷ (p + q ) ) ) <= (2000000 * (((p - 1 ) * 1415 ) + ((q + 1 ) - 1 ) ) )) ”
  &&  “ (RCProgress n_pre m_pre p (q + 1 ) (ans + ((m_pre ÷ q ) ÷ (p + q ) ) ) ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) >= (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  TT && emp 
|--
  “ (RCProgress n_pre m_pre p (q + 1 ) (ans + ((m_pre ÷ q ) ÷ (p + q ) ) ) ) ”
  &&  “ ((ans + ((m_pre ÷ q ) ÷ (p + q ) ) ) <= (2000000 * (((p - 1 ) * 1415 ) + ((q + 1 ) - 1 ) ) )) ”
  &&  “ (0 <= (ans + ((m_pre ÷ q ) ÷ (p + q ) ) )) ”
  &&  emp
).

Definition solver_entail_wit_4_2_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) >= (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  (RCProgress n_pre m_pre p (q + 1 ) (ans + ((m_pre ÷ q ) ÷ (p + q ) ) ) )
.

Definition solver_entail_wit_4_2_split_goal_2 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) >= (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  ((ans + ((m_pre ÷ q ) ÷ (p + q ) ) ) <= (2000000 * (((p - 1 ) * 1415 ) + ((q + 1 ) - 1 ) ) ))
.

Definition solver_entail_wit_4_2_split_goal_3 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : ((n_pre ÷ p ) >= (m_pre ÷ q ))) (PreH2 : (retval = 1)) (PreH3 : (retval = (RCgcd (p) (q)))) (PreH4 : ((q * q ) < m_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 2000000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 2000000)) (PreH9 : (1 <= p)) (PreH10 : (p <= 1415)) (PreH11 : ((p * p ) < n_pre)) (PreH12 : (1 <= q)) (PreH13 : (q <= 1415)) (PreH14 : (0 <= ans)) (PreH15 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH16 : (RCProgress n_pre m_pre p q ans )),
  (0 <= (ans + ((m_pre ÷ q ) ÷ (p + q ) ) ))
.

Definition solver_entail_wit_4_3 :=
(
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (retval = (RCgcd (p) (q)))) (PreH3 : ((q * q ) < m_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 2000000)) (PreH8 : (1 <= p)) (PreH9 : (p <= 1415)) (PreH10 : ((p * p ) < n_pre)) (PreH11 : (1 <= q)) (PreH12 : (q <= 1415)) (PreH13 : (0 <= ans)) (PreH14 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH15 : (RCProgress n_pre m_pre p q ans )),
  TT && emp 
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 2000000) ”
  &&  “ (1 <= p) ”
  &&  “ (p <= 1415) ”
  &&  “ ((p * p ) < n_pre) ”
  &&  “ (1 <= (q + 1 )) ”
  &&  “ ((q + 1 ) <= 1415) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= (2000000 * (((p - 1 ) * 1415 ) + ((q + 1 ) - 1 ) ) )) ”
  &&  “ (RCProgress n_pre m_pre p (q + 1 ) ans ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (retval = (RCgcd (p) (q)))) (PreH3 : ((q * q ) < m_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 2000000)) (PreH8 : (1 <= p)) (PreH9 : (p <= 1415)) (PreH10 : ((p * p ) < n_pre)) (PreH11 : (1 <= q)) (PreH12 : (q <= 1415)) (PreH13 : (0 <= ans)) (PreH14 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH15 : (RCProgress n_pre m_pre p q ans )),
  TT && emp 
|--
  “ (RCProgress n_pre m_pre p (q + 1 ) ans ) ”
  &&  emp
).

Definition solver_entail_wit_4_3_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (retval = (RCgcd (p) (q)))) (PreH3 : ((q * q ) < m_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 2000000)) (PreH8 : (1 <= p)) (PreH9 : (p <= 1415)) (PreH10 : ((p * p ) < n_pre)) (PreH11 : (1 <= q)) (PreH12 : (q <= 1415)) (PreH13 : (0 <= ans)) (PreH14 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH15 : (RCProgress n_pre m_pre p q ans )),
  (RCProgress n_pre m_pre p (q + 1 ) ans )
.

Definition solver_return_wit_1 :=
(
forall (n_pre: Z) (m_pre: Z) (ans: Z) (p: Z) (PreH1 : ((p * p ) >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 2000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 2000000)) (PreH6 : (1 <= p)) (PreH7 : (p <= 1415)) (PreH8 : (0 <= ans)) (PreH9 : (ans <= (2000000 * ((p - 1 ) * 1415 ) ))) (PreH10 : (RCProgress n_pre m_pre p 1 ans )),
  TT && emp 
|--
  “ (Spec n_pre m_pre ans ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (m_pre: Z) (ans: Z) (p: Z) (PreH1 : ((p * p ) >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 2000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 2000000)) (PreH6 : (1 <= p)) (PreH7 : (p <= 1415)) (PreH8 : (0 <= ans)) (PreH9 : (ans <= (2000000 * ((p - 1 ) * 1415 ) ))) (PreH10 : (RCProgress n_pre m_pre p 1 ans )),
  TT && emp 
|--
  “ (Spec n_pre m_pre ans ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (p: Z) (PreH1 : ((p * p ) >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 2000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 2000000)) (PreH6 : (1 <= p)) (PreH7 : (p <= 1415)) (PreH8 : (0 <= ans)) (PreH9 : (ans <= (2000000 * ((p - 1 ) * 1415 ) ))) (PreH10 : (RCProgress n_pre m_pre p 1 ans )),
  (Spec n_pre m_pre ans )
.

Definition solver_partial_solve_wit_1_pure :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (PreH1 : ((q * q ) < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 2000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 2000000)) (PreH6 : (1 <= p)) (PreH7 : (p <= 1415)) (PreH8 : ((p * p ) < n_pre)) (PreH9 : (1 <= q)) (PreH10 : (q <= 1415)) (PreH11 : (0 <= ans)) (PreH12 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH13 : (RCProgress n_pre m_pre p q ans )),
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
|--
  “ (1 <= p) ”
  &&  “ (p <= 2000000) ”
  &&  “ (1 <= q) ”
  &&  “ (q <= 2000000) ”
.

Definition solver_partial_solve_wit_1_aux :=
forall (n_pre: Z) (m_pre: Z) (ans: Z) (q: Z) (p: Z) (PreH1 : ((q * q ) < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 2000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 2000000)) (PreH6 : (1 <= p)) (PreH7 : (p <= 1415)) (PreH8 : ((p * p ) < n_pre)) (PreH9 : (1 <= q)) (PreH10 : (q <= 1415)) (PreH11 : (0 <= ans)) (PreH12 : (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) ))) (PreH13 : (RCProgress n_pre m_pre p q ans )),
  TT && emp 
|--
  “ (1 <= p) ”
  &&  “ (p <= 2000000) ”
  &&  “ (1 <= q) ”
  &&  “ (q <= 2000000) ”
  &&  “ ((q * q ) < m_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= 2000000) ”
  &&  “ (1 <= m_pre) ”
  &&  “ (m_pre <= 2000000) ”
  &&  “ (1 <= p) ”
  &&  “ (p <= 1415) ”
  &&  “ ((p * p ) < n_pre) ”
  &&  “ (1 <= q) ”
  &&  “ (q <= 1415) ”
  &&  “ (0 <= ans) ”
  &&  “ (ans <= (2000000 * (((p - 1 ) * 1415 ) + (q - 1 ) ) )) ”
  &&  “ (RCProgress n_pre m_pre p q ans ) ”
  &&  emp
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Module Type VC_Correct.


Axiom proof_of_gcd_int_safety_wit_1 : gcd_int_safety_wit_1.
Axiom proof_of_gcd_int_entail_wit_1 : gcd_int_entail_wit_1.
Axiom proof_of_gcd_int_entail_wit_2 : gcd_int_entail_wit_2.
Axiom proof_of_gcd_int_return_wit_1 : gcd_int_return_wit_1.
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
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.

End VC_Correct.
