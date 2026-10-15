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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P027_1800D_remove_two_letters_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (text: (@list Z)) (PreH1 : (3 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  ((( &( "answer" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition solver_safety_wit_2 := 
forall (n_pre: Z) (s_pre: Z) (text: (@list Z)) (PreH1 : (3 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  ((( &( "answer" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_3 := 
forall (n_pre: Z) (s_pre: Z) (text: (@list Z)) (PreH1 : (3 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "answer" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (n_pre: Z) (s_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : (3 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (0 <= i)) (PreH6 : ((i + 2 ) <= n_pre)) (PreH7 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH8 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH9 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH10 : (1 <= answer)) (PreH11 : (answer <= (n_pre - 1 ))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ ((i + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 2 )) ”
.

Definition solver_safety_wit_5 := 
forall (n_pre: Z) (s_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : (3 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (0 <= i)) (PreH6 : ((i + 2 ) <= n_pre)) (PreH7 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH8 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH9 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH10 : (1 <= answer)) (PreH11 : (answer <= (n_pre - 1 ))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_6 := 
forall (n_pre: Z) (s_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((i + 2 ) < n_pre)) (PreH2 : (3 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : (0 <= i)) (PreH7 : ((i + 2 ) <= n_pre)) (PreH8 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH9 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH10 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH11 : (1 <= answer)) (PreH12 : (answer <= (n_pre - 1 ))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((i + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 2 )) ”
.

Definition solver_safety_wit_7 := 
forall (n_pre: Z) (s_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((i + 2 ) < n_pre)) (PreH2 : (3 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : (0 <= i)) (PreH7 : ((i + 2 ) <= n_pre)) (PreH8 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH9 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH10 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH11 : (1 <= answer)) (PreH12 : (answer <= (n_pre - 1 ))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_8 := 
forall (n_pre: Z) (s_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = (Znth (i + 2 ) (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : ((i + 2 ) < n_pre)) (PreH3 : (3 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 2 ) <= n_pre)) (PreH9 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH10 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH11 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH12 : (1 <= answer)) (PreH13 : (answer <= (n_pre - 1 ))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((answer - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (answer - 1 )) ”
.

Definition solver_safety_wit_9 := 
forall (n_pre: Z) (s_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = (Znth (i + 2 ) (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : ((i + 2 ) < n_pre)) (PreH3 : (3 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 2 ) <= n_pre)) (PreH9 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH10 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH11 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH12 : (1 <= answer)) (PreH13 : (answer <= (n_pre - 1 ))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> (answer - 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_10 := 
forall (n_pre: Z) (s_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> (Znth (i + 2 ) (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : ((i + 2 ) < n_pre)) (PreH3 : (3 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 2 ) <= n_pre)) (PreH9 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH10 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH11 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH12 : (1 <= answer)) (PreH13 : (answer <= (n_pre - 1 ))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (n_pre: Z) (s_pre: Z) (text: (@list Z)) (PreH1 : (3 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (3 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((0 + 2 ) <= n_pre) ” 
  &&  “ (0 <= (EqualGapTwoCount (text) (0))) ” 
  &&  “ ((EqualGapTwoCount (text) (0)) <= 0) ” 
  &&  “ ((n_pre - 1 ) = ((n_pre - 1 ) - (EqualGapTwoCount (text) (0)) )) ” 
  &&  “ (1 <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) <= (n_pre - 1 )) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (n_pre: Z) (text: (@list Z)) (PreH1 : (3 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  TT && emp 
|--
  “ ((n_pre - 1 ) = ((n_pre - 1 ) - (EqualGapTwoCount (text) (0)) )) ” 
  &&  “ ((EqualGapTwoCount (text) (0)) <= 0) ” 
  &&  “ (0 <= (EqualGapTwoCount (text) (0))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (text: (@list Z)) (PreH1 : (3 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  ((n_pre - 1 ) = ((n_pre - 1 ) - (EqualGapTwoCount (text) (0)) ))
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (text: (@list Z)) (PreH1 : (3 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  ((EqualGapTwoCount (text) (0)) <= 0)
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (text: (@list Z)) (PreH1 : (3 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  (0 <= (EqualGapTwoCount (text) (0)))
.

Definition solver_entail_wit_1_split_goal_4 := 
forall (n_pre: Z) (text: (@list Z)) (PreH1 : (3 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 200000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))
.

Definition solver_entail_wit_2_1 := 
(
forall (n_pre: Z) (s_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = (Znth (i + 2 ) (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : ((i + 2 ) < n_pre)) (PreH3 : (3 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 2 ) <= n_pre)) (PreH9 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH10 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH11 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH12 : (1 <= answer)) (PreH13 : (answer <= (n_pre - 1 ))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (3 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ (((i + 1 ) + 2 ) <= n_pre) ” 
  &&  “ (0 <= (EqualGapTwoCount (text) ((i + 1 )))) ” 
  &&  “ ((EqualGapTwoCount (text) ((i + 1 ))) <= (i + 1 )) ” 
  &&  “ ((answer - 1 ) = ((n_pre - 1 ) - (EqualGapTwoCount (text) ((i + 1 ))) )) ” 
  &&  “ (1 <= (answer - 1 )) ” 
  &&  “ ((answer - 1 ) <= (n_pre - 1 )) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (n_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = (Znth (i + 2 ) (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : ((i + 2 ) < n_pre)) (PreH3 : (3 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 2 ) <= n_pre)) (PreH9 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH10 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH11 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH12 : (1 <= answer)) (PreH13 : (answer <= (n_pre - 1 ))) ,
  TT && emp 
|--
  “ (1 <= (answer - 1 )) ” 
  &&  “ ((answer - 1 ) = ((n_pre - 1 ) - (EqualGapTwoCount (text) ((i + 1 ))) )) ” 
  &&  “ ((EqualGapTwoCount (text) ((i + 1 ))) <= (i + 1 )) ” 
  &&  “ (0 <= (EqualGapTwoCount (text) ((i + 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 := 
forall (n_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = (Znth (i + 2 ) (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : ((i + 2 ) < n_pre)) (PreH3 : (3 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 2 ) <= n_pre)) (PreH9 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH10 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH11 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH12 : (1 <= answer)) (PreH13 : (answer <= (n_pre - 1 ))) ,
  (1 <= (answer - 1 ))
.

Definition solver_entail_wit_2_1_split_goal_2 := 
forall (n_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = (Znth (i + 2 ) (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : ((i + 2 ) < n_pre)) (PreH3 : (3 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 2 ) <= n_pre)) (PreH9 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH10 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH11 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH12 : (1 <= answer)) (PreH13 : (answer <= (n_pre - 1 ))) ,
  ((answer - 1 ) = ((n_pre - 1 ) - (EqualGapTwoCount (text) ((i + 1 ))) ))
.

Definition solver_entail_wit_2_1_split_goal_3 := 
forall (n_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = (Znth (i + 2 ) (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : ((i + 2 ) < n_pre)) (PreH3 : (3 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 2 ) <= n_pre)) (PreH9 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH10 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH11 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH12 : (1 <= answer)) (PreH13 : (answer <= (n_pre - 1 ))) ,
  ((EqualGapTwoCount (text) ((i + 1 ))) <= (i + 1 ))
.

Definition solver_entail_wit_2_1_split_goal_4 := 
forall (n_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = (Znth (i + 2 ) (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : ((i + 2 ) < n_pre)) (PreH3 : (3 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 2 ) <= n_pre)) (PreH9 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH10 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH11 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH12 : (1 <= answer)) (PreH13 : (answer <= (n_pre - 1 ))) ,
  (0 <= (EqualGapTwoCount (text) ((i + 1 ))))
.

Definition solver_entail_wit_2_2 := 
(
forall (n_pre: Z) (s_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> (Znth (i + 2 ) (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : ((i + 2 ) < n_pre)) (PreH3 : (3 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 2 ) <= n_pre)) (PreH9 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH10 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH11 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH12 : (1 <= answer)) (PreH13 : (answer <= (n_pre - 1 ))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (3 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ (((i + 1 ) + 2 ) <= n_pre) ” 
  &&  “ (0 <= (EqualGapTwoCount (text) ((i + 1 )))) ” 
  &&  “ ((EqualGapTwoCount (text) ((i + 1 ))) <= (i + 1 )) ” 
  &&  “ (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) ((i + 1 ))) )) ” 
  &&  “ (1 <= answer) ” 
  &&  “ (answer <= (n_pre - 1 )) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (n_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> (Znth (i + 2 ) (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : ((i + 2 ) < n_pre)) (PreH3 : (3 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 2 ) <= n_pre)) (PreH9 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH10 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH11 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH12 : (1 <= answer)) (PreH13 : (answer <= (n_pre - 1 ))) ,
  TT && emp 
|--
  “ (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) ((i + 1 ))) )) ” 
  &&  “ ((EqualGapTwoCount (text) ((i + 1 ))) <= (i + 1 )) ” 
  &&  “ (0 <= (EqualGapTwoCount (text) ((i + 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 := 
forall (n_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> (Znth (i + 2 ) (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : ((i + 2 ) < n_pre)) (PreH3 : (3 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 2 ) <= n_pre)) (PreH9 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH10 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH11 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH12 : (1 <= answer)) (PreH13 : (answer <= (n_pre - 1 ))) ,
  (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) ((i + 1 ))) ))
.

Definition solver_entail_wit_2_2_split_goal_2 := 
forall (n_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> (Znth (i + 2 ) (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : ((i + 2 ) < n_pre)) (PreH3 : (3 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 2 ) <= n_pre)) (PreH9 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH10 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH11 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH12 : (1 <= answer)) (PreH13 : (answer <= (n_pre - 1 ))) ,
  ((EqualGapTwoCount (text) ((i + 1 ))) <= (i + 1 ))
.

Definition solver_entail_wit_2_2_split_goal_3 := 
forall (n_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> (Znth (i + 2 ) (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : ((i + 2 ) < n_pre)) (PreH3 : (3 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 2 ) <= n_pre)) (PreH9 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH10 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH11 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH12 : (1 <= answer)) (PreH13 : (answer <= (n_pre - 1 ))) ,
  (0 <= (EqualGapTwoCount (text) ((i + 1 ))))
.

Definition solver_return_wit_1 := 
(
forall (n_pre: Z) (s_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((i + 2 ) >= n_pre)) (PreH2 : (3 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : (0 <= i)) (PreH7 : ((i + 2 ) <= n_pre)) (PreH8 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH9 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH10 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH11 : (1 <= answer)) (PreH12 : (answer <= (n_pre - 1 ))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (Spec text answer ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (n_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((i + 2 ) >= n_pre)) (PreH2 : (3 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : (0 <= i)) (PreH7 : ((i + 2 ) <= n_pre)) (PreH8 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH9 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH10 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH11 : (1 <= answer)) (PreH12 : (answer <= (n_pre - 1 ))) ,
  TT && emp 
|--
  “ (Spec text answer ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((i + 2 ) >= n_pre)) (PreH2 : (3 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : (0 <= i)) (PreH7 : ((i + 2 ) <= n_pre)) (PreH8 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH9 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH10 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH11 : (1 <= answer)) (PreH12 : (answer <= (n_pre - 1 ))) ,
  (Spec text answer )
.

Definition solver_partial_solve_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((i + 2 ) < n_pre)) (PreH2 : (3 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : (0 <= i)) (PreH7 : ((i + 2 ) <= n_pre)) (PreH8 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH9 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH10 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH11 : (1 <= answer)) (PreH12 : (answer <= (n_pre - 1 ))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ ((i + 2 ) < n_pre) ” 
  &&  “ (3 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 2 ) <= n_pre) ” 
  &&  “ (0 <= (EqualGapTwoCount (text) (i))) ” 
  &&  “ ((EqualGapTwoCount (text) (i)) <= i) ” 
  &&  “ (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) )) ” 
  &&  “ (1 <= answer) ” 
  &&  “ (answer <= (n_pre - 1 )) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_2 := 
forall (n_pre: Z) (s_pre: Z) (text: (@list Z)) (answer: Z) (i: Z) (PreH1 : ((i + 2 ) < n_pre)) (PreH2 : (3 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 200000)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122)))) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : (0 <= i)) (PreH7 : ((i + 2 ) <= n_pre)) (PreH8 : (0 <= (EqualGapTwoCount (text) (i)))) (PreH9 : ((EqualGapTwoCount (text) (i)) <= i)) (PreH10 : (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) ))) (PreH11 : (1 <= answer)) (PreH12 : (answer <= (n_pre - 1 ))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ ((i + 2 ) < n_pre) ” 
  &&  “ (3 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (text)))) -> ((97 <= (Znth k text 0)) /\ ((Znth k text 0) <= 122))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 2 ) <= n_pre) ” 
  &&  “ (0 <= (EqualGapTwoCount (text) (i))) ” 
  &&  “ ((EqualGapTwoCount (text) (i)) <= i) ” 
  &&  “ (answer = ((n_pre - 1 ) - (EqualGapTwoCount (text) (i)) )) ” 
  &&  “ (1 <= answer) ” 
  &&  “ (answer <= (n_pre - 1 )) ”
  &&  (((s_pre + ((i + 2 ) * sizeof(CHAR)))) # Char  |-> (Znth (i + 2 ) (app (text) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre (i + 2 ) 0 (n_pre + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.

End VC_Correct.
