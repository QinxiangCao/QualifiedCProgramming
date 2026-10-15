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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P006_867A_between_the_offices_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (days: (@list Z)) (PreH1 : ((Znth (0) (days) (0)) = (Znth (0) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH2 : ((Znth ((n_pre - 1 )) (days) (0)) = (Znth ((n_pre - 1 )) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH3 : (n_pre = (Zlength (days)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i days 0) = 83) \/ ((Znth i days 0) = 70)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (days) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (n_pre: Z) (s_pre: Z) (days: (@list Z)) (PreH1 : ((Znth (0) (days) (0)) = (Znth (0) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH2 : ((Znth ((n_pre - 1 )) (days) (0)) = (Znth ((n_pre - 1 )) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH3 : (n_pre = (Zlength (days)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i days 0) = 83) \/ ((Znth i days 0) = 70)))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (days) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (83 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 83) ”
.

Definition solver_safety_wit_3 := 
forall (n_pre: Z) (s_pre: Z) (days: (@list Z)) (PreH1 : ((Znth 0 (app (days) ((cons (0) ((@nil Z))))) 0) = 83)) (PreH2 : ((Znth (0) (days) (0)) = (Znth (0) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH3 : ((Znth ((n_pre - 1 )) (days) (0)) = (Znth ((n_pre - 1 )) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH4 : (n_pre = (Zlength (days)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i days 0) = 83) \/ ((Znth i days 0) = 70)))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (days) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition solver_safety_wit_4 := 
forall (n_pre: Z) (s_pre: Z) (days: (@list Z)) (PreH1 : ((Znth 0 (app (days) ((cons (0) ((@nil Z))))) 0) = 83)) (PreH2 : ((Znth (0) (days) (0)) = (Znth (0) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH3 : ((Znth ((n_pre - 1 )) (days) (0)) = (Znth ((n_pre - 1 )) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH4 : (n_pre = (Zlength (days)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i days 0) = 83) \/ ((Znth i days 0) = 70)))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (days) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
forall (n_pre: Z) (s_pre: Z) (days: (@list Z)) (PreH1 : ((Znth 0 (app (days) ((cons (0) ((@nil Z))))) 0) = 83)) (PreH2 : ((Znth (0) (days) (0)) = (Znth (0) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH3 : ((Znth ((n_pre - 1 )) (days) (0)) = (Znth ((n_pre - 1 )) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH4 : (n_pre = (Zlength (days)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i days 0) = 83) \/ ((Znth i days 0) = 70)))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (days) ((cons (0) ((@nil Z))))) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (70 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 70) ”
.

Definition solver_entail_wit_1 := 
(
forall (n_pre: Z) (s_pre: Z) (days: (@list Z)) (PreH1 : (n_pre = (Zlength (days)))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i days 0) = 83) \/ ((Znth i days 0) = 70)))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (days) ((cons (0) ((@nil Z))))) )
|--
  “ ((Znth (0) (days) (0)) = (Znth (0) ((app (days) ((cons (0) ((@nil Z)))))) (0))) ” 
  &&  “ ((Znth ((n_pre - 1 )) (days) (0)) = (Znth ((n_pre - 1 )) ((app (days) ((cons (0) ((@nil Z)))))) (0))) ” 
  &&  “ (n_pre = (Zlength (days))) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i days 0) = 83) \/ ((Znth i days 0) = 70))) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (days) ((cons (0) ((@nil Z))))) )
) \/
(
forall (n_pre: Z) (days: (@list Z)) (PreH1 : (n_pre = (Zlength (days)))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i days 0) = 83) \/ ((Znth i days 0) = 70)))) ,
  TT && emp 
|--
  “ ((Znth ((n_pre - 1 )) (days) (0)) = (Znth ((n_pre - 1 )) ((app (days) ((cons (0) ((@nil Z)))))) (0))) ” 
  &&  “ ((Znth (0) (days) (0)) = (Znth (0) ((app (days) ((cons (0) ((@nil Z)))))) (0))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (days: (@list Z)) (PreH1 : (n_pre = (Zlength (days)))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i days 0) = 83) \/ ((Znth i days 0) = 70)))) ,
  ((Znth ((n_pre - 1 )) (days) (0)) = (Znth ((n_pre - 1 )) ((app (days) ((cons (0) ((@nil Z)))))) (0)))
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (days: (@list Z)) (PreH1 : (n_pre = (Zlength (days)))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i days 0) = 83) \/ ((Znth i days 0) = 70)))) ,
  ((Znth (0) (days) (0)) = (Znth (0) ((app (days) ((cons (0) ((@nil Z)))))) (0)))
.

Definition solver_return_wit_1 := 
(
forall (n_pre: Z) (s_pre: Z) (days: (@list Z)) (PreH1 : ((Znth 0 (app (days) ((cons (0) ((@nil Z))))) 0) <> 83)) (PreH2 : ((Znth (0) (days) (0)) = (Znth (0) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH3 : ((Znth ((n_pre - 1 )) (days) (0)) = (Znth ((n_pre - 1 )) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH4 : (n_pre = (Zlength (days)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i days 0) = 83) \/ ((Znth i days 0) = 70)))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (days) ((cons (0) ((@nil Z))))) )
|--
  EX (answer: bool) ,
  “ (Spec days answer ) ” 
  &&  “ (VerdictCode answer 0 ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (days) ((cons (0) ((@nil Z))))) )
) \/
(
forall (n_pre: Z) (days: (@list Z)) (PreH1 : ((Znth 0 (app (days) ((cons (0) ((@nil Z))))) 0) <> 83)) (PreH2 : ((Znth (0) (days) (0)) = (Znth (0) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH3 : ((Znth ((n_pre - 1 )) (days) (0)) = (Znth ((n_pre - 1 )) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH4 : (n_pre = (Zlength (days)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i days 0) = 83) \/ ((Znth i days 0) = 70)))) ,
  TT && emp 
|--
  EX (answer: bool) ,
  “ (Spec days answer ) ” 
  &&  “ (VerdictCode answer 0 ) ”
  &&  emp
).

Definition solver_return_wit_2 := 
(
forall (n_pre: Z) (s_pre: Z) (days: (@list Z)) (PreH1 : ((Znth (n_pre - 1 ) (app (days) ((cons (0) ((@nil Z))))) 0) = 70)) (PreH2 : ((Znth 0 (app (days) ((cons (0) ((@nil Z))))) 0) = 83)) (PreH3 : ((Znth (0) (days) (0)) = (Znth (0) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH4 : ((Znth ((n_pre - 1 )) (days) (0)) = (Znth ((n_pre - 1 )) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH5 : (n_pre = (Zlength (days)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i days 0) = 83) \/ ((Znth i days 0) = 70)))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (days) ((cons (0) ((@nil Z))))) )
|--
  EX (answer: bool) ,
  “ (Spec days answer ) ” 
  &&  “ (VerdictCode answer 1 ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (days) ((cons (0) ((@nil Z))))) )
) \/
(
forall (n_pre: Z) (days: (@list Z)) (PreH1 : ((Znth (n_pre - 1 ) (app (days) ((cons (0) ((@nil Z))))) 0) = 70)) (PreH2 : ((Znth 0 (app (days) ((cons (0) ((@nil Z))))) 0) = 83)) (PreH3 : ((Znth (0) (days) (0)) = (Znth (0) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH4 : ((Znth ((n_pre - 1 )) (days) (0)) = (Znth ((n_pre - 1 )) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH5 : (n_pre = (Zlength (days)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i days 0) = 83) \/ ((Znth i days 0) = 70)))) ,
  TT && emp 
|--
  EX (answer: bool) ,
  “ (Spec days answer ) ” 
  &&  “ (VerdictCode answer 1 ) ”
  &&  emp
).

Definition solver_return_wit_3 := 
(
forall (n_pre: Z) (s_pre: Z) (days: (@list Z)) (PreH1 : ((Znth (n_pre - 1 ) (app (days) ((cons (0) ((@nil Z))))) 0) <> 70)) (PreH2 : ((Znth 0 (app (days) ((cons (0) ((@nil Z))))) 0) = 83)) (PreH3 : ((Znth (0) (days) (0)) = (Znth (0) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH4 : ((Znth ((n_pre - 1 )) (days) (0)) = (Znth ((n_pre - 1 )) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH5 : (n_pre = (Zlength (days)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i days 0) = 83) \/ ((Znth i days 0) = 70)))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (days) ((cons (0) ((@nil Z))))) )
|--
  EX (answer: bool) ,
  “ (Spec days answer ) ” 
  &&  “ (VerdictCode answer 0 ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (days) ((cons (0) ((@nil Z))))) )
) \/
(
forall (n_pre: Z) (days: (@list Z)) (PreH1 : ((Znth (n_pre - 1 ) (app (days) ((cons (0) ((@nil Z))))) 0) <> 70)) (PreH2 : ((Znth 0 (app (days) ((cons (0) ((@nil Z))))) 0) = 83)) (PreH3 : ((Znth (0) (days) (0)) = (Znth (0) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH4 : ((Znth ((n_pre - 1 )) (days) (0)) = (Znth ((n_pre - 1 )) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH5 : (n_pre = (Zlength (days)))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i days 0) = 83) \/ ((Znth i days 0) = 70)))) ,
  TT && emp 
|--
  EX (answer: bool) ,
  “ (Spec days answer ) ” 
  &&  “ (VerdictCode answer 0 ) ”
  &&  emp
).

Definition solver_partial_solve_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (days: (@list Z)) (PreH1 : ((Znth (0) (days) (0)) = (Znth (0) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH2 : ((Znth ((n_pre - 1 )) (days) (0)) = (Znth ((n_pre - 1 )) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH3 : (n_pre = (Zlength (days)))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i days 0) = 83) \/ ((Znth i days 0) = 70)))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (days) ((cons (0) ((@nil Z))))) )
|--
  “ ((Znth (0) (days) (0)) = (Znth (0) ((app (days) ((cons (0) ((@nil Z)))))) (0))) ” 
  &&  “ ((Znth ((n_pre - 1 )) (days) (0)) = (Znth ((n_pre - 1 )) ((app (days) ((cons (0) ((@nil Z)))))) (0))) ” 
  &&  “ (n_pre = (Zlength (days))) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i days 0) = 83) \/ ((Znth i days 0) = 70))) ”
  &&  (((s_pre + (0 * sizeof(CHAR)))) # Char  |-> (Znth 0 (app (days) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre 0 0 (n_pre + 1 ) (app (days) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_2 := 
forall (n_pre: Z) (s_pre: Z) (days: (@list Z)) (PreH1 : ((Znth 0 (app (days) ((cons (0) ((@nil Z))))) 0) = 83)) (PreH2 : ((Znth (0) (days) (0)) = (Znth (0) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH3 : ((Znth ((n_pre - 1 )) (days) (0)) = (Znth ((n_pre - 1 )) ((app (days) ((cons (0) ((@nil Z)))))) (0)))) (PreH4 : (n_pre = (Zlength (days)))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i days 0) = 83) \/ ((Znth i days 0) = 70)))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (days) ((cons (0) ((@nil Z))))) )
|--
  “ ((Znth 0 (app (days) ((cons (0) ((@nil Z))))) 0) = 83) ” 
  &&  “ ((Znth (0) (days) (0)) = (Znth (0) ((app (days) ((cons (0) ((@nil Z)))))) (0))) ” 
  &&  “ ((Znth ((n_pre - 1 )) (days) (0)) = (Znth ((n_pre - 1 )) ((app (days) ((cons (0) ((@nil Z)))))) (0))) ” 
  &&  “ (n_pre = (Zlength (days))) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i days 0) = 83) \/ ((Znth i days 0) = 70))) ”
  &&  (((s_pre + ((n_pre - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (n_pre - 1 ) (app (days) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre (n_pre - 1 ) 0 (n_pre + 1 ) (app (days) ((cons (0) ((@nil Z))))) )
.

Module Type VC_Correct.


Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.

End VC_Correct.
