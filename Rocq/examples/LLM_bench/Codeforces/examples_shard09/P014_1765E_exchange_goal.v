From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P014_1765E_exchange_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (n_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre > b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_2 :=
forall (n_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
|--
  “ ((((n_pre + a_pre ) - 1 ) <> (INT64_MIN)) \/ (a_pre <> (-1))) ”
  &&  “ (a_pre <> 0) ”
.

Definition solver_safety_wit_3 :=
forall (n_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
|--
  “ (((n_pre + a_pre ) - 1 ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= ((n_pre + a_pre ) - 1 )) ”
.

Definition solver_safety_wit_4 :=
forall (n_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
|--
  “ ((n_pre + a_pre ) <= INT64_MAX) ”
  &&  “ ((INT64_MIN) <= (n_pre + a_pre )) ”
.

Definition solver_safety_wit_5 :=
forall (n_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)),
  ((( &( "n" ) )) # Int64  |-> n_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
  **  ((( &( "b" ) )) # Int64  |-> b_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_return_wit_1 :=
(
forall (n_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)),
  TT && emp 
|--
  “ (Spec n_pre a_pre b_pre (((n_pre + a_pre ) - 1 ) ÷ a_pre ) ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)),
  TT && emp 
|--
  “ (Spec n_pre a_pre b_pre (((n_pre + a_pre ) - 1 ) ÷ a_pre ) ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (n_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre <= b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)),
  (Spec n_pre a_pre b_pre (((n_pre + a_pre ) - 1 ) ÷ a_pre ) )
.

Definition solver_return_wit_2 :=
(
forall (n_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre > b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)),
  TT && emp 
|--
  “ (Spec n_pre a_pre b_pre 1 ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre > b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)),
  TT && emp 
|--
  “ (Spec n_pre a_pre b_pre 1 ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 :=
forall (n_pre: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre > b_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 10000000)) (PreH4 : (1 <= a_pre)) (PreH5 : (a_pre <= 50)) (PreH6 : (1 <= b_pre)) (PreH7 : (b_pre <= 50)),
  (Spec n_pre a_pre b_pre 1 )
.

Module Type VC_Correct.


Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.

End VC_Correct.
