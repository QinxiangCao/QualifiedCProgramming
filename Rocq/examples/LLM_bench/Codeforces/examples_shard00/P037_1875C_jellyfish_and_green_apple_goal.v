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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P037_1875C_jellyfish_and_green_apple_lib.
Local Open Scope sac.

(*----- Function gcdll -----*)

Definition gcdll_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 1000000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b <> 0)) ,
  ((( &( "t" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int64  |-> a)
  **  ((( &( "b" ) )) # Int64  |-> b)
|--
  “ ((a <> (INT64_MIN)) \/ (b <> (-1))) ” 
  &&  “ (b <> 0) ”
.

Definition gcdll_entail_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (1 <= a_pre)) (PreH2 : (a_pre <= 1000000000)) (PreH3 : (1 <= b_pre)) (PreH4 : (b_pre <= 1000000000)) ,
  TT && emp 
|--
  “ (1 <= a_pre) ” 
  &&  “ (a_pre <= 1000000000) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= 1000000000) ” 
  &&  “ ((GcdValue (a_pre) (b_pre)) = (GcdValue (a_pre) (b_pre))) ”
  &&  emp
.

Definition gcdll_entail_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 1000000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b <> 0)) ,
  TT && emp 
|--
  “ (1 <= b) ” 
  &&  “ (b <= 1000000000) ” 
  &&  “ (0 <= (a % ( b ) )) ” 
  &&  “ ((a % ( b ) ) <= 1000000000) ” 
  &&  “ ((GcdValue (b) ((a % ( b ) ))) = (GcdValue (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 1000000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b <> 0)) ,
  TT && emp 
|--
  “ ((GcdValue (b) ((a % ( b ) ))) = (GcdValue (a_pre) (b_pre))) ” 
  &&  “ ((a % ( b ) ) <= 1000000000) ” 
  &&  “ (0 <= (a % ( b ) )) ”
  &&  emp
).

Definition gcdll_entail_wit_2_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 1000000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b <> 0)) ,
  ((GcdValue (b) ((a % ( b ) ))) = (GcdValue (a_pre) (b_pre)))
.

Definition gcdll_entail_wit_2_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 1000000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b <> 0)) ,
  ((a % ( b ) ) <= 1000000000)
.

Definition gcdll_entail_wit_2_split_goal_3 := 
forall (b_pre: Z) (a_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 1000000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b <> 0)) ,
  (0 <= (a % ( b ) ))
.

Definition gcdll_return_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 1000000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b = 0)) ,
  TT && emp 
|--
  “ (a = (GcdValue (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 1000000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b = 0)) ,
  TT && emp 
|--
  “ (a = (GcdValue (a_pre) (b_pre))) ”
  &&  emp
).

Definition gcdll_return_wit_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (b: Z) (a: Z) (PreH1 : (1 <= a)) (PreH2 : (a <= 1000000000)) (PreH3 : (0 <= b)) (PreH4 : (b <= 1000000000)) (PreH5 : ((GcdValue (a) (b)) = (GcdValue (a_pre) (b_pre)))) (PreH6 : (b = 0)) ,
  (a = (GcdValue (a_pre) (b_pre)))
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
(
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) ,
  ((( &( "d" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ ((m_pre <> (INT64_MIN)) \/ (retval <> (-1))) ” 
  &&  “ (retval <> 0) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) ,
  ((( &( "d" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ ((m_pre <> (INT64_MIN)) \/ (retval <> (-1))) ” 
  &&  “ (retval <> 0) ”
).

Definition solver_safety_wit_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) ,
  ((( &( "d" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ ((m_pre <> (INT64_MIN)) \/ (retval <> (-1))) ”
.

Definition solver_safety_wit_1_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) ,
  ((( &( "d" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (retval <> 0) ”
.

Definition solver_safety_wit_2 := 
(
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) ,
  ((( &( "d" ) )) # Int64  |-> (m_pre ÷ retval ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (((m_pre ÷ retval ) - 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((m_pre ÷ retval ) - 1 )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) ,
  ((( &( "d" ) )) # Int64  |-> (m_pre ÷ retval ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (((m_pre ÷ retval ) - 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((m_pre ÷ retval ) - 1 )) ”
).

Definition solver_safety_wit_2_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) ,
  ((( &( "d" ) )) # Int64  |-> (m_pre ÷ retval ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (((m_pre ÷ retval ) - 1 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_2_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) ,
  ((( &( "d" ) )) # Int64  |-> (m_pre ÷ retval ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ ((INT64_MIN) <= ((m_pre ÷ retval ) - 1 )) ”
.

Definition solver_safety_wit_3 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) ,
  ((( &( "d" ) )) # Int64  |-> (m_pre ÷ retval ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_4 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Z.land (m_pre ÷ retval ) ((m_pre ÷ retval ) - 1 )) <> 0)) ,
  ((( &( "d" ) )) # Int64  |-> (m_pre ÷ retval ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_5 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Z.land (m_pre ÷ retval ) ((m_pre ÷ retval ) - 1 )) <> 0)) ,
  ((( &( "d" ) )) # Int64  |-> (m_pre ÷ retval ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Z.land (m_pre ÷ retval ) ((m_pre ÷ retval ) - 1 )) = 0)) ,
  ((( &( "d" ) )) # Int64  |-> (m_pre ÷ retval ))
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ ((n_pre <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_7 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Z.land (m_pre ÷ retval ) ((m_pre ÷ retval ) - 1 )) = 0)) ,
  ((( &( "answer" ) )) # Int64  |->_)
  **  ((( &( "d" ) )) # Int64  |-> (m_pre ÷ retval ))
  **  ((( &( "n" ) )) # Int64  |-> (n_pre % ( m_pre ) ))
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 := 
forall (m_pre: Z) (n_pre: Z) (answer: Z) (n: Z) (d: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (d = (m_pre ÷ (GcdValue (n_pre) (m_pre)) ))) (PreH6 : (PowerOfTwo d )) (PreH7 : (0 <= n)) (PreH8 : (n < m_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= 30000000000)) (PreH11 : (DyadicRemainderPrefix (n_pre % ( m_pre ) ) m_pre n answer )) (PreH12 : (n <> 0)) ,
  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
|--
  “ ((answer + n ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (answer + n )) ”
.

Definition solver_safety_wit_9 := 
forall (m_pre: Z) (n_pre: Z) (answer: Z) (n: Z) (d: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (d = (m_pre ÷ (GcdValue (n_pre) (m_pre)) ))) (PreH6 : (PowerOfTwo d )) (PreH7 : (0 <= n)) (PreH8 : (n < m_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= 30000000000)) (PreH11 : (DyadicRemainderPrefix (n_pre % ( m_pre ) ) m_pre n answer )) (PreH12 : (n <> 0)) ,
  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "answer" ) )) # Int64  |-> (answer + n ))
|--
  “ (((2 * n ) <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_10 := 
forall (m_pre: Z) (n_pre: Z) (answer: Z) (n: Z) (d: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (d = (m_pre ÷ (GcdValue (n_pre) (m_pre)) ))) (PreH6 : (PowerOfTwo d )) (PreH7 : (0 <= n)) (PreH8 : (n < m_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= 30000000000)) (PreH11 : (DyadicRemainderPrefix (n_pre % ( m_pre ) ) m_pre n answer )) (PreH12 : (n <> 0)) ,
  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "answer" ) )) # Int64  |-> (answer + n ))
|--
  “ ((2 * n ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (2 * n )) ”
.

Definition solver_safety_wit_11 := 
forall (m_pre: Z) (n_pre: Z) (answer: Z) (n: Z) (d: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (d = (m_pre ÷ (GcdValue (n_pre) (m_pre)) ))) (PreH6 : (PowerOfTwo d )) (PreH7 : (0 <= n)) (PreH8 : (n < m_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= 30000000000)) (PreH11 : (DyadicRemainderPrefix (n_pre % ( m_pre ) ) m_pre n answer )) (PreH12 : (n <> 0)) ,
  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "d" ) )) # Int64  |-> d)
  **  ((( &( "n" ) )) # Int64  |-> n)
  **  ((( &( "answer" ) )) # Int64  |-> (answer + n ))
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_entail_wit_1 := 
(
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Z.land (m_pre ÷ retval ) ((m_pre ÷ retval ) - 1 )) = 0)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000000000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ ((m_pre ÷ retval ) = (m_pre ÷ (GcdValue (n_pre) (m_pre)) )) ” 
  &&  “ (PowerOfTwo (m_pre ÷ retval ) ) ” 
  &&  “ (0 <= (n_pre % ( m_pre ) )) ” 
  &&  “ ((n_pre % ( m_pre ) ) < m_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 30000000000) ” 
  &&  “ (DyadicRemainderPrefix (n_pre % ( m_pre ) ) m_pre (n_pre % ( m_pre ) ) 0 ) ”
  &&  emp
) \/
(
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Z.land (m_pre ÷ retval ) ((m_pre ÷ retval ) - 1 )) = 0)) ,
  TT && emp 
|--
  “ (DyadicRemainderPrefix (n_pre % ( m_pre ) ) m_pre (n_pre % ( m_pre ) ) 0 ) ” 
  &&  “ ((n_pre % ( m_pre ) ) < m_pre) ” 
  &&  “ (0 <= (n_pre % ( m_pre ) )) ” 
  &&  “ (PowerOfTwo (m_pre ÷ retval ) ) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Z.land (m_pre ÷ retval ) ((m_pre ÷ retval ) - 1 )) = 0)) ,
  (DyadicRemainderPrefix (n_pre % ( m_pre ) ) m_pre (n_pre % ( m_pre ) ) 0 )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Z.land (m_pre ÷ retval ) ((m_pre ÷ retval ) - 1 )) = 0)) ,
  ((n_pre % ( m_pre ) ) < m_pre)
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Z.land (m_pre ÷ retval ) ((m_pre ÷ retval ) - 1 )) = 0)) ,
  (0 <= (n_pre % ( m_pre ) ))
.

Definition solver_entail_wit_1_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Z.land (m_pre ÷ retval ) ((m_pre ÷ retval ) - 1 )) = 0)) ,
  (PowerOfTwo (m_pre ÷ retval ) )
.

Definition solver_entail_wit_2 := 
(
forall (m_pre: Z) (n_pre: Z) (answer: Z) (n: Z) (d: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (d = (m_pre ÷ (GcdValue (n_pre) (m_pre)) ))) (PreH6 : (PowerOfTwo d )) (PreH7 : (0 <= n)) (PreH8 : (n < m_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= 30000000000)) (PreH11 : (DyadicRemainderPrefix (n_pre % ( m_pre ) ) m_pre n answer )) (PreH12 : (n <> 0)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000000000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (d = (m_pre ÷ (GcdValue (n_pre) (m_pre)) )) ” 
  &&  “ (PowerOfTwo d ) ” 
  &&  “ (0 <= ((2 * n ) % ( m_pre ) )) ” 
  &&  “ (((2 * n ) % ( m_pre ) ) < m_pre) ” 
  &&  “ (0 <= (answer + n )) ” 
  &&  “ ((answer + n ) <= 30000000000) ” 
  &&  “ (DyadicRemainderPrefix (n_pre % ( m_pre ) ) m_pre ((2 * n ) % ( m_pre ) ) (answer + n ) ) ”
  &&  emp
) \/
(
forall (m_pre: Z) (n_pre: Z) (answer: Z) (n: Z) (d: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (d = (m_pre ÷ (GcdValue (n_pre) (m_pre)) ))) (PreH6 : (PowerOfTwo d )) (PreH7 : (0 <= n)) (PreH8 : (n < m_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= 30000000000)) (PreH11 : (DyadicRemainderPrefix (n_pre % ( m_pre ) ) m_pre n answer )) (PreH12 : (n <> 0)) ,
  TT && emp 
|--
  “ (DyadicRemainderPrefix (n_pre % ( m_pre ) ) m_pre ((2 * n ) % ( m_pre ) ) (answer + n ) ) ” 
  &&  “ ((answer + n ) <= 30000000000) ” 
  &&  “ (((2 * n ) % ( m_pre ) ) < m_pre) ” 
  &&  “ (0 <= ((2 * n ) % ( m_pre ) )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (answer: Z) (n: Z) (d: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (d = (m_pre ÷ (GcdValue (n_pre) (m_pre)) ))) (PreH6 : (PowerOfTwo d )) (PreH7 : (0 <= n)) (PreH8 : (n < m_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= 30000000000)) (PreH11 : (DyadicRemainderPrefix (n_pre % ( m_pre ) ) m_pre n answer )) (PreH12 : (n <> 0)) ,
  (DyadicRemainderPrefix (n_pre % ( m_pre ) ) m_pre ((2 * n ) % ( m_pre ) ) (answer + n ) )
.

Definition solver_entail_wit_2_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (answer: Z) (n: Z) (d: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (d = (m_pre ÷ (GcdValue (n_pre) (m_pre)) ))) (PreH6 : (PowerOfTwo d )) (PreH7 : (0 <= n)) (PreH8 : (n < m_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= 30000000000)) (PreH11 : (DyadicRemainderPrefix (n_pre % ( m_pre ) ) m_pre n answer )) (PreH12 : (n <> 0)) ,
  ((answer + n ) <= 30000000000)
.

Definition solver_entail_wit_2_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (answer: Z) (n: Z) (d: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (d = (m_pre ÷ (GcdValue (n_pre) (m_pre)) ))) (PreH6 : (PowerOfTwo d )) (PreH7 : (0 <= n)) (PreH8 : (n < m_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= 30000000000)) (PreH11 : (DyadicRemainderPrefix (n_pre % ( m_pre ) ) m_pre n answer )) (PreH12 : (n <> 0)) ,
  (((2 * n ) % ( m_pre ) ) < m_pre)
.

Definition solver_entail_wit_2_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (answer: Z) (n: Z) (d: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (d = (m_pre ÷ (GcdValue (n_pre) (m_pre)) ))) (PreH6 : (PowerOfTwo d )) (PreH7 : (0 <= n)) (PreH8 : (n < m_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= 30000000000)) (PreH11 : (DyadicRemainderPrefix (n_pre % ( m_pre ) ) m_pre n answer )) (PreH12 : (n <> 0)) ,
  (0 <= ((2 * n ) % ( m_pre ) ))
.

Definition solver_return_wit_1 := 
(
forall (m_pre: Z) (n_pre: Z) (answer: Z) (n: Z) (d: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (d = (m_pre ÷ (GcdValue (n_pre) (m_pre)) ))) (PreH6 : (PowerOfTwo d )) (PreH7 : (0 <= n)) (PreH8 : (n < m_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= 30000000000)) (PreH11 : (DyadicRemainderPrefix (n_pre % ( m_pre ) ) m_pre n answer )) (PreH12 : (n = 0)) ,
  TT && emp 
|--
  “ (Spec n_pre m_pre answer ) ”
  &&  emp
) \/
(
forall (m_pre: Z) (n_pre: Z) (answer: Z) (n: Z) (d: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (d = (m_pre ÷ (GcdValue (n_pre) (m_pre)) ))) (PreH6 : (PowerOfTwo d )) (PreH7 : (0 <= n)) (PreH8 : (n < m_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= 30000000000)) (PreH11 : (DyadicRemainderPrefix (n_pre % ( m_pre ) ) m_pre n answer )) (PreH12 : (n = 0)) ,
  TT && emp 
|--
  “ (Spec n_pre m_pre answer ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (answer: Z) (n: Z) (d: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (d = (m_pre ÷ (GcdValue (n_pre) (m_pre)) ))) (PreH6 : (PowerOfTwo d )) (PreH7 : (0 <= n)) (PreH8 : (n < m_pre)) (PreH9 : (0 <= answer)) (PreH10 : (answer <= 30000000000)) (PreH11 : (DyadicRemainderPrefix (n_pre % ( m_pre ) ) m_pre n answer )) (PreH12 : (n = 0)) ,
  (Spec n_pre m_pre answer )
.

Definition solver_return_wit_2 := 
(
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Z.land (m_pre ÷ retval ) ((m_pre ÷ retval ) - 1 )) <> 0)) ,
  TT && emp 
|--
  “ (Spec n_pre m_pre (-1) ) ”
  &&  emp
) \/
(
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Z.land (m_pre ÷ retval ) ((m_pre ÷ retval ) - 1 )) <> 0)) ,
  TT && emp 
|--
  “ (Spec n_pre m_pre (-1) ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (retval = (GcdValue (n_pre) (m_pre)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000000000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Z.land (m_pre ÷ retval ) ((m_pre ÷ retval ) - 1 )) <> 0)) ,
  (Spec n_pre m_pre (-1) )
.

Definition solver_partial_solve_wit_1_pure := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((( &( "d" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000000000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000000000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000000000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000000000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ”
  &&  emp
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Module Type VC_Correct.


Axiom proof_of_gcdll_safety_wit_1 : gcdll_safety_wit_1.
Axiom proof_of_gcdll_entail_wit_1 : gcdll_entail_wit_1.
Axiom proof_of_gcdll_entail_wit_2 : gcdll_entail_wit_2.
Axiom proof_of_gcdll_return_wit_1 : gcdll_return_wit_1.
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.

End VC_Correct.
