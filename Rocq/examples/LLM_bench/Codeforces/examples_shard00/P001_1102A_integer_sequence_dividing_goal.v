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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P001_1102A_integer_sequence_dividing_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2000000000)) ,
  ((( &( "n" ) )) # Int64  |-> n_pre)
|--
  “ (((n_pre * (n_pre + 1 ) ) <> (INT64_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_2 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2000000000)) ,
  ((( &( "n" ) )) # Int64  |-> n_pre)
|--
  “ ((n_pre * (n_pre + 1 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (n_pre * (n_pre + 1 ) )) ”
.

Definition solver_safety_wit_3 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2000000000)) ,
  ((( &( "n" ) )) # Int64  |-> n_pre)
|--
  “ ((n_pre + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (n_pre + 1 )) ”
.

Definition solver_safety_wit_4 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2000000000)) ,
  ((( &( "n" ) )) # Int64  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2000000000)) ,
  ((( &( "n" ) )) # Int64  |-> n_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_6 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2000000000)) ,
  ((( &( "n" ) )) # Int64  |-> n_pre)
|--
  “ (1 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 1) ”
.

Definition solver_return_wit_1 := 
(
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2000000000)) ,
  TT && emp 
|--
  “ (Spec n_pre (Z.land ((n_pre * (n_pre + 1 ) ) ÷ 2 ) 1) ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2000000000)) ,
  TT && emp 
|--
  “ (Spec n_pre (Z.land ((n_pre * (n_pre + 1 ) ) ÷ 2 ) 1) ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2000000000)) ,
  (Spec n_pre (Z.land ((n_pre * (n_pre + 1 ) ) ÷ 2 ) 1) )
.

Module Type VC_Correct.


Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.

End VC_Correct.
