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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100)) ,
  ((( &( "days" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (n: Z) (days: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (0 <= days)) (PreH6 : (days <= 200)) (PreH7 : (0 <= n)) (PreH8 : (n <= 100)) (PreH9 : (n = ((n_pre + (days ÷ m_pre ) ) - days ))) (PreH10 : forall (d: Z) , (((1 <= d) /\ (d <= days)) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0))) ,
  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "days" ) )) # Int  |-> days)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (m_pre: Z) (n_pre: Z) (n: Z) (days: Z) (PreH1 : (n > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= days)) (PreH7 : (days <= 200)) (PreH8 : (0 <= n)) (PreH9 : (n <= 100)) (PreH10 : (n = ((n_pre + (days ÷ m_pre ) ) - days ))) (PreH11 : forall (d: Z) , (((1 <= d) /\ (d <= days)) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0))) ,
  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "days" ) )) # Int  |-> days)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ ((days + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (days + 1 )) ”
.

Definition solver_safety_wit_4 := 
forall (m_pre: Z) (n_pre: Z) (n: Z) (days: Z) (PreH1 : (n > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= days)) (PreH7 : (days <= 200)) (PreH8 : (0 <= n)) (PreH9 : (n <= 100)) (PreH10 : (n = ((n_pre + (days ÷ m_pre ) ) - days ))) (PreH11 : forall (d: Z) , (((1 <= d) /\ (d <= days)) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0))) ,
  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "days" ) )) # Int  |-> (days + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition solver_safety_wit_5 := 
forall (m_pre: Z) (n_pre: Z) (n: Z) (days: Z) (PreH1 : (n > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= days)) (PreH7 : (days <= 200)) (PreH8 : (0 <= n)) (PreH9 : (n <= 100)) (PreH10 : (n = ((n_pre + (days ÷ m_pre ) ) - days ))) (PreH11 : forall (d: Z) , (((1 <= d) /\ (d <= days)) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0))) ,
  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "days" ) )) # Int  |-> (days + 1 ))
  **  ((( &( "n" ) )) # Int  |-> (n - 1 ))
|--
  “ (((days + 1 ) <> (INT_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_6 := 
forall (m_pre: Z) (n_pre: Z) (n: Z) (days: Z) (PreH1 : (n > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= days)) (PreH7 : (days <= 200)) (PreH8 : (0 <= n)) (PreH9 : (n <= 100)) (PreH10 : (n = ((n_pre + (days ÷ m_pre ) ) - days ))) (PreH11 : forall (d: Z) , (((1 <= d) /\ (d <= days)) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0))) ,
  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "days" ) )) # Int  |-> (days + 1 ))
  **  ((( &( "n" ) )) # Int  |-> (n - 1 ))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 := 
forall (m_pre: Z) (n_pre: Z) (n: Z) (days: Z) (PreH1 : (((days + 1 ) % ( m_pre ) ) = 0)) (PreH2 : (n > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= days)) (PreH8 : (days <= 200)) (PreH9 : (0 <= n)) (PreH10 : (n <= 100)) (PreH11 : (n = ((n_pre + (days ÷ m_pre ) ) - days ))) (PreH12 : forall (d: Z) , (((1 <= d) /\ (d <= days)) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0))) ,
  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "days" ) )) # Int  |-> (days + 1 ))
  **  ((( &( "n" ) )) # Int  |-> (n - 1 ))
|--
  “ (((n - 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n - 1 ) + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 200) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = ((n_pre + (0 ÷ m_pre ) ) - 0 )) ” 
  &&  “ forall (d: Z) , (((1 <= d) /\ (d <= 0)) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0)) ”
  &&  emp
) \/
(
forall (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100)) ,
  TT && emp 
|--
  “ forall (d: Z) , (((1 <= d) /\ (d <= 0)) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0)) ” 
  &&  “ (n_pre = ((n_pre + (0 ÷ m_pre ) ) - 0 )) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100)) ,
  forall (d: Z) , (((1 <= d) /\ (d <= 0)) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0))
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100)) ,
  (n_pre = ((n_pre + (0 ÷ m_pre ) ) - 0 ))
.

Definition solver_entail_wit_2_1 := 
(
forall (m_pre: Z) (n_pre: Z) (n: Z) (days: Z) (PreH1 : (((days + 1 ) % ( m_pre ) ) = 0)) (PreH2 : (n > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= days)) (PreH8 : (days <= 200)) (PreH9 : (0 <= n)) (PreH10 : (n <= 100)) (PreH11 : (n = ((n_pre + (days ÷ m_pre ) ) - days ))) (PreH12 : forall (d: Z) , (((1 <= d) /\ (d <= days)) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0))) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ (0 <= (days + 1 )) ” 
  &&  “ ((days + 1 ) <= 200) ” 
  &&  “ (0 <= ((n - 1 ) + 1 )) ” 
  &&  “ (((n - 1 ) + 1 ) <= 100) ” 
  &&  “ (((n - 1 ) + 1 ) = ((n_pre + ((days + 1 ) ÷ m_pre ) ) - (days + 1 ) )) ” 
  &&  “ forall (d: Z) , (((1 <= d) /\ (d <= (days + 1 ))) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0)) ”
  &&  emp
) \/
(
forall (m_pre: Z) (n_pre: Z) (n: Z) (days: Z) (PreH1 : (((days + 1 ) % ( m_pre ) ) = 0)) (PreH2 : (n > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= days)) (PreH8 : (days <= 200)) (PreH9 : (0 <= n)) (PreH10 : (n <= 100)) (PreH11 : (n = ((n_pre + (days ÷ m_pre ) ) - days ))) (PreH12 : forall (d: Z) , (((1 <= d) /\ (d <= days)) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0))) ,
  TT && emp 
|--
  “ (((((n_pre + (days ÷ m_pre ) ) - days ) - 1 ) + 1 ) = ((n_pre + ((days + 1 ) ÷ m_pre ) ) - (days + 1 ) )) ” 
  &&  “ ((days + 1 ) <= 200) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (n: Z) (days: Z) (PreH1 : (((days + 1 ) % ( m_pre ) ) = 0)) (PreH2 : (n > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= days)) (PreH8 : (days <= 200)) (PreH9 : (0 <= n)) (PreH10 : (n <= 100)) (PreH11 : (n = ((n_pre + (days ÷ m_pre ) ) - days ))) (PreH12 : forall (d: Z) , (((1 <= d) /\ (d <= days)) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0))) ,
  (((((n_pre + (days ÷ m_pre ) ) - days ) - 1 ) + 1 ) = ((n_pre + ((days + 1 ) ÷ m_pre ) ) - (days + 1 ) ))
.

Definition solver_entail_wit_2_1_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (n: Z) (days: Z) (PreH1 : (((days + 1 ) % ( m_pre ) ) = 0)) (PreH2 : (n > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= days)) (PreH8 : (days <= 200)) (PreH9 : (0 <= n)) (PreH10 : (n <= 100)) (PreH11 : (n = ((n_pre + (days ÷ m_pre ) ) - days ))) (PreH12 : forall (d: Z) , (((1 <= d) /\ (d <= days)) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0))) ,
  ((days + 1 ) <= 200)
.

Definition solver_entail_wit_2_2 := 
(
forall (m_pre: Z) (n_pre: Z) (n: Z) (days: Z) (PreH1 : (((days + 1 ) % ( m_pre ) ) <> 0)) (PreH2 : (n > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= days)) (PreH8 : (days <= 200)) (PreH9 : (0 <= n)) (PreH10 : (n <= 100)) (PreH11 : (n = ((n_pre + (days ÷ m_pre ) ) - days ))) (PreH12 : forall (d: Z) , (((1 <= d) /\ (d <= days)) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0))) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ (0 <= (days + 1 )) ” 
  &&  “ ((days + 1 ) <= 200) ” 
  &&  “ (0 <= (n - 1 )) ” 
  &&  “ ((n - 1 ) <= 100) ” 
  &&  “ ((n - 1 ) = ((n_pre + ((days + 1 ) ÷ m_pre ) ) - (days + 1 ) )) ” 
  &&  “ forall (d: Z) , (((1 <= d) /\ (d <= (days + 1 ))) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0)) ”
  &&  emp
) \/
(
forall (m_pre: Z) (n_pre: Z) (n: Z) (days: Z) (PreH1 : (((days + 1 ) % ( m_pre ) ) <> 0)) (PreH2 : (n > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= days)) (PreH8 : (days <= 200)) (PreH9 : (0 <= n)) (PreH10 : (n <= 100)) (PreH11 : (n = ((n_pre + (days ÷ m_pre ) ) - days ))) (PreH12 : forall (d: Z) , (((1 <= d) /\ (d <= days)) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0))) ,
  TT && emp 
|--
  “ ((((n_pre + (days ÷ m_pre ) ) - days ) - 1 ) = ((n_pre + ((days + 1 ) ÷ m_pre ) ) - (days + 1 ) )) ” 
  &&  “ ((days + 1 ) <= 200) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (n: Z) (days: Z) (PreH1 : (((days + 1 ) % ( m_pre ) ) <> 0)) (PreH2 : (n > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= days)) (PreH8 : (days <= 200)) (PreH9 : (0 <= n)) (PreH10 : (n <= 100)) (PreH11 : (n = ((n_pre + (days ÷ m_pre ) ) - days ))) (PreH12 : forall (d: Z) , (((1 <= d) /\ (d <= days)) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0))) ,
  ((((n_pre + (days ÷ m_pre ) ) - days ) - 1 ) = ((n_pre + ((days + 1 ) ÷ m_pre ) ) - (days + 1 ) ))
.

Definition solver_entail_wit_2_2_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (n: Z) (days: Z) (PreH1 : (((days + 1 ) % ( m_pre ) ) <> 0)) (PreH2 : (n > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : (0 <= days)) (PreH8 : (days <= 200)) (PreH9 : (0 <= n)) (PreH10 : (n <= 100)) (PreH11 : (n = ((n_pre + (days ÷ m_pre ) ) - days ))) (PreH12 : forall (d: Z) , (((1 <= d) /\ (d <= days)) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0))) ,
  ((days + 1 ) <= 200)
.

Definition solver_return_wit_1 := 
(
forall (m_pre: Z) (n_pre: Z) (n: Z) (days: Z) (PreH1 : (n <= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= days)) (PreH7 : (days <= 200)) (PreH8 : (0 <= n)) (PreH9 : (n <= 100)) (PreH10 : (n = ((n_pre + (days ÷ m_pre ) ) - days ))) (PreH11 : forall (d: Z) , (((1 <= d) /\ (d <= days)) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0))) ,
  TT && emp 
|--
  “ (Spec n_pre m_pre days ) ”
  &&  emp
) \/
(
forall (m_pre: Z) (n_pre: Z) (n: Z) (days: Z) (PreH1 : (n <= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= days)) (PreH7 : (days <= 200)) (PreH8 : (0 <= n)) (PreH9 : (n <= 100)) (PreH10 : (n = ((n_pre + (days ÷ m_pre ) ) - days ))) (PreH11 : forall (d: Z) , (((1 <= d) /\ (d <= days)) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0))) ,
  TT && emp 
|--
  “ (Spec n_pre m_pre days ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (n: Z) (days: Z) (PreH1 : (n <= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : (0 <= days)) (PreH7 : (days <= 200)) (PreH8 : (0 <= n)) (PreH9 : (n <= 100)) (PreH10 : (n = ((n_pre + (days ÷ m_pre ) ) - days ))) (PreH11 : forall (d: Z) , (((1 <= d) /\ (d <= days)) -> (((n_pre + ((d - 1 ) ÷ m_pre ) ) - (d - 1 ) ) > 0))) ,
  (Spec n_pre m_pre days )
.

Module Type VC_Correct.


Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.

End VC_Correct.
