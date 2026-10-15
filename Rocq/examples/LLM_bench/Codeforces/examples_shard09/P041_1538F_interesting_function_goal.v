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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P041_1538F_interesting_function_lib.
Local Open Scope sac.

(*----- Function changed_upto -----*)

Definition changed_upto_safety_wit_1 := 
forall (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000)) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition changed_upto_safety_wit_2 := 
forall (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000)) ,
  ((( &( "p" ) )) # Int64  |->_)
  **  ((( &( "total" ) )) # Int64  |-> 0)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition changed_upto_safety_wit_3 := 
forall (x_pre: Z) (total: Z) (p: Z) (PreH1 : (p <= x_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) (PreH4 : (1 <= p)) (PreH5 : (p <= 10000000000)) (PreH6 : (0 <= total)) (PreH7 : (total <= 1111111111)) (PreH8 : (DecimalPlacePrefix x_pre p total )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "p" ) )) # Int64  |-> p)
  **  ((( &( "total" ) )) # Int64  |-> (total + (x_pre ÷ p ) ))
|--
  “ ((p * 10 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (p * 10 )) ”
.

Definition changed_upto_safety_wit_4 := 
forall (x_pre: Z) (total: Z) (p: Z) (PreH1 : (p <= x_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) (PreH4 : (1 <= p)) (PreH5 : (p <= 10000000000)) (PreH6 : (0 <= total)) (PreH7 : (total <= 1111111111)) (PreH8 : (DecimalPlacePrefix x_pre p total )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "p" ) )) # Int64  |-> p)
  **  ((( &( "total" ) )) # Int64  |-> (total + (x_pre ÷ p ) ))
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition changed_upto_safety_wit_5 := 
(
forall (x_pre: Z) (total: Z) (p: Z) (PreH1 : (p <= x_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) (PreH4 : (1 <= p)) (PreH5 : (p <= 10000000000)) (PreH6 : (0 <= total)) (PreH7 : (total <= 1111111111)) (PreH8 : (DecimalPlacePrefix x_pre p total )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "p" ) )) # Int64  |-> p)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((total + (x_pre ÷ p ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (total + (x_pre ÷ p ) )) ”
) \/
(
forall (x_pre: Z) (total: Z) (p: Z) (PreH1 : (p <= x_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) (PreH4 : (1 <= p)) (PreH5 : (p <= 10000000000)) (PreH6 : (0 <= total)) (PreH7 : (total <= 1111111111)) (PreH8 : (DecimalPlacePrefix x_pre p total )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "p" ) )) # Int64  |-> p)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((total + (x_pre ÷ p ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (total + (x_pre ÷ p ) )) ”
).

Definition changed_upto_safety_wit_5_split_goal_1 := 
forall (x_pre: Z) (total: Z) (p: Z) (PreH1 : (p <= x_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) (PreH4 : (1 <= p)) (PreH5 : (p <= 10000000000)) (PreH6 : (0 <= total)) (PreH7 : (total <= 1111111111)) (PreH8 : (DecimalPlacePrefix x_pre p total )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "p" ) )) # Int64  |-> p)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((total + (x_pre ÷ p ) ) <= INT64_MAX) ”
.

Definition changed_upto_safety_wit_5_split_goal_2 := 
forall (x_pre: Z) (total: Z) (p: Z) (PreH1 : (p <= x_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) (PreH4 : (1 <= p)) (PreH5 : (p <= 10000000000)) (PreH6 : (0 <= total)) (PreH7 : (total <= 1111111111)) (PreH8 : (DecimalPlacePrefix x_pre p total )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "p" ) )) # Int64  |-> p)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((INT64_MIN) <= (total + (x_pre ÷ p ) )) ”
.

Definition changed_upto_safety_wit_6 := 
forall (x_pre: Z) (total: Z) (p: Z) (PreH1 : (p <= x_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) (PreH4 : (1 <= p)) (PreH5 : (p <= 10000000000)) (PreH6 : (0 <= total)) (PreH7 : (total <= 1111111111)) (PreH8 : (DecimalPlacePrefix x_pre p total )) ,
  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "p" ) )) # Int64  |-> p)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((x_pre <> (INT64_MIN)) \/ (p <> (-1))) ” 
  &&  “ (p <> 0) ”
.

Definition changed_upto_entail_wit_1 := 
(
forall (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000)) ,
  TT && emp 
|--
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 10000000000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1111111111) ” 
  &&  “ (DecimalPlacePrefix x_pre 1 0 ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000)) ,
  TT && emp 
|--
  “ (DecimalPlacePrefix x_pre 1 0 ) ”
  &&  emp
).

Definition changed_upto_entail_wit_1_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000)) ,
  (DecimalPlacePrefix x_pre 1 0 )
.

Definition changed_upto_entail_wit_2 := 
(
forall (x_pre: Z) (total: Z) (p: Z) (PreH1 : (p <= x_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) (PreH4 : (1 <= p)) (PreH5 : (p <= 10000000000)) (PreH6 : (0 <= total)) (PreH7 : (total <= 1111111111)) (PreH8 : (DecimalPlacePrefix x_pre p total )) ,
  TT && emp 
|--
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 1000000000) ” 
  &&  “ (1 <= (p * 10 )) ” 
  &&  “ ((p * 10 ) <= 10000000000) ” 
  &&  “ (0 <= (total + (x_pre ÷ p ) )) ” 
  &&  “ ((total + (x_pre ÷ p ) ) <= 1111111111) ” 
  &&  “ (DecimalPlacePrefix x_pre (p * 10 ) (total + (x_pre ÷ p ) ) ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (total: Z) (p: Z) (PreH1 : (p <= x_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) (PreH4 : (1 <= p)) (PreH5 : (p <= 10000000000)) (PreH6 : (0 <= total)) (PreH7 : (total <= 1111111111)) (PreH8 : (DecimalPlacePrefix x_pre p total )) ,
  TT && emp 
|--
  “ (DecimalPlacePrefix x_pre (p * 10 ) (total + (x_pre ÷ p ) ) ) ” 
  &&  “ ((total + (x_pre ÷ p ) ) <= 1111111111) ” 
  &&  “ (0 <= (total + (x_pre ÷ p ) )) ”
  &&  emp
).

Definition changed_upto_entail_wit_2_split_goal_1 := 
forall (x_pre: Z) (total: Z) (p: Z) (PreH1 : (p <= x_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) (PreH4 : (1 <= p)) (PreH5 : (p <= 10000000000)) (PreH6 : (0 <= total)) (PreH7 : (total <= 1111111111)) (PreH8 : (DecimalPlacePrefix x_pre p total )) ,
  (DecimalPlacePrefix x_pre (p * 10 ) (total + (x_pre ÷ p ) ) )
.

Definition changed_upto_entail_wit_2_split_goal_2 := 
forall (x_pre: Z) (total: Z) (p: Z) (PreH1 : (p <= x_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) (PreH4 : (1 <= p)) (PreH5 : (p <= 10000000000)) (PreH6 : (0 <= total)) (PreH7 : (total <= 1111111111)) (PreH8 : (DecimalPlacePrefix x_pre p total )) ,
  ((total + (x_pre ÷ p ) ) <= 1111111111)
.

Definition changed_upto_entail_wit_2_split_goal_3 := 
forall (x_pre: Z) (total: Z) (p: Z) (PreH1 : (p <= x_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) (PreH4 : (1 <= p)) (PreH5 : (p <= 10000000000)) (PreH6 : (0 <= total)) (PreH7 : (total <= 1111111111)) (PreH8 : (DecimalPlacePrefix x_pre p total )) ,
  (0 <= (total + (x_pre ÷ p ) ))
.

Definition changed_upto_return_wit_1 := 
(
forall (x_pre: Z) (total: Z) (p: Z) (PreH1 : (p > x_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) (PreH4 : (1 <= p)) (PreH5 : (p <= 10000000000)) (PreH6 : (0 <= total)) (PreH7 : (total <= 1111111111)) (PreH8 : (DecimalPlacePrefix x_pre p total )) ,
  TT && emp 
|--
  “ (0 <= total) ” 
  &&  “ (total <= 1111111111) ” 
  &&  “ (DecimalPrefixTotal x_pre total ) ”
  &&  emp
) \/
(
forall (x_pre: Z) (total: Z) (p: Z) (PreH1 : (p > x_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) (PreH4 : (1 <= p)) (PreH5 : (p <= 10000000000)) (PreH6 : (0 <= total)) (PreH7 : (total <= 1111111111)) (PreH8 : (DecimalPlacePrefix x_pre p total )) ,
  TT && emp 
|--
  “ (DecimalPrefixTotal x_pre total ) ”
  &&  emp
).

Definition changed_upto_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (total: Z) (p: Z) (PreH1 : (p > x_pre)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000)) (PreH4 : (1 <= p)) (PreH5 : (p <= 10000000000)) (PreH6 : (0 <= total)) (PreH7 : (total <= 1111111111)) (PreH8 : (DecimalPlacePrefix x_pre p total )) ,
  (DecimalPrefixTotal x_pre total )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (r_pre: Z) (l_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1111111111)) (PreH3 : (DecimalPrefixTotal l_pre retval_2 )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1111111111)) (PreH6 : (DecimalPrefixTotal r_pre retval )) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre < r_pre)) (PreH9 : (r_pre <= 1000000000)) ,
  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
|--
  “ ((retval - retval_2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (retval - retval_2 )) ”
.

Definition solver_return_wit_1 := 
(
forall (r_pre: Z) (l_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1111111111)) (PreH3 : (DecimalPrefixTotal l_pre retval_2 )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1111111111)) (PreH6 : (DecimalPrefixTotal r_pre retval )) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre < r_pre)) (PreH9 : (r_pre <= 1000000000)) ,
  TT && emp 
|--
  “ (Spec l_pre r_pre (retval - retval_2 ) ) ”
  &&  emp
) \/
(
forall (r_pre: Z) (l_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1111111111)) (PreH3 : (DecimalPrefixTotal l_pre retval_2 )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1111111111)) (PreH6 : (DecimalPrefixTotal r_pre retval )) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre < r_pre)) (PreH9 : (r_pre <= 1000000000)) ,
  TT && emp 
|--
  “ (Spec l_pre r_pre (retval - retval_2 ) ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (r_pre: Z) (l_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1111111111)) (PreH3 : (DecimalPrefixTotal l_pre retval_2 )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1111111111)) (PreH6 : (DecimalPrefixTotal r_pre retval )) (PreH7 : (1 <= l_pre)) (PreH8 : (l_pre < r_pre)) (PreH9 : (r_pre <= 1000000000)) ,
  (Spec l_pre r_pre (retval - retval_2 ) )
.

Definition solver_partial_solve_wit_1_pure := 
forall (r_pre: Z) (l_pre: Z) (PreH1 : (1 <= l_pre)) (PreH2 : (l_pre < r_pre)) (PreH3 : (r_pre <= 1000000000)) ,
  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
|--
  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= 1000000000) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (r_pre: Z) (l_pre: Z) (PreH1 : (1 <= l_pre)) (PreH2 : (l_pre < r_pre)) (PreH3 : (r_pre <= 1000000000)) ,
  TT && emp 
|--
  “ (1 <= r_pre) ” 
  &&  “ (r_pre <= 1000000000) ” 
  &&  “ (1 <= l_pre) ” 
  &&  “ (l_pre < r_pre) ” 
  &&  “ (r_pre <= 1000000000) ”
  &&  emp
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2_pure := 
forall (r_pre: Z) (l_pre: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1111111111)) (PreH3 : (DecimalPrefixTotal r_pre retval )) (PreH4 : (1 <= l_pre)) (PreH5 : (l_pre < r_pre)) (PreH6 : (r_pre <= 1000000000)) ,
  ((( &( "l" ) )) # Int64  |-> l_pre)
  **  ((( &( "r" ) )) # Int64  |-> r_pre)
|--
  “ (1 <= l_pre) ” 
  &&  “ (l_pre <= 1000000000) ”
.

Definition solver_partial_solve_wit_2_aux := 
forall (r_pre: Z) (l_pre: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1111111111)) (PreH3 : (DecimalPrefixTotal r_pre retval )) (PreH4 : (1 <= l_pre)) (PreH5 : (l_pre < r_pre)) (PreH6 : (r_pre <= 1000000000)) ,
  TT && emp 
|--
  “ (1 <= l_pre) ” 
  &&  “ (l_pre <= 1000000000) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1111111111) ” 
  &&  “ (DecimalPrefixTotal r_pre retval ) ” 
  &&  “ (1 <= l_pre) ” 
  &&  “ (l_pre < r_pre) ” 
  &&  “ (r_pre <= 1000000000) ”
  &&  emp
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Module Type VC_Correct.


Axiom proof_of_changed_upto_safety_wit_1 : changed_upto_safety_wit_1.
Axiom proof_of_changed_upto_safety_wit_2 : changed_upto_safety_wit_2.
Axiom proof_of_changed_upto_safety_wit_3 : changed_upto_safety_wit_3.
Axiom proof_of_changed_upto_safety_wit_4 : changed_upto_safety_wit_4.
Axiom proof_of_changed_upto_safety_wit_5 : changed_upto_safety_wit_5.
Axiom proof_of_changed_upto_safety_wit_6 : changed_upto_safety_wit_6.
Axiom proof_of_changed_upto_entail_wit_1 : changed_upto_entail_wit_1.
Axiom proof_of_changed_upto_entail_wit_2 : changed_upto_entail_wit_2.
Axiom proof_of_changed_upto_return_wit_1 : changed_upto_return_wit_1.
Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.

End VC_Correct.
