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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P024_1104B_game_with_string_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (s_pre: Z) (text: (@list Z)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) ,
  ((( &( "moves" ) )) # Int  |->_)
  **  ((( &( "top" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full ( &( "stack" ) ) 100005 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (s_pre: Z) (text: (@list Z)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) ,
  ((( &( "top" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full ( &( "stack" ) ) 100005 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (s_pre: Z) (text: (@list Z)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "moves" ) )) # Int  |-> 0)
  **  ((( &( "top" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full ( &( "stack" ) ) 100005 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : (top <> 0)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced)))) (PreH10 : (0 <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves ) ))) (PreH13 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) (PreH14 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "moves" ) )) # Int  |-> moves)
  **  (CharArray.full ( &( "stack" ) ) top reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
|--
  “ ((top - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top - 1 )) ”
.

Definition solver_safety_wit_5 := 
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : (top <> 0)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced)))) (PreH10 : (0 <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves ) ))) (PreH13 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) (PreH14 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "moves" ) )) # Int  |-> moves)
  **  (CharArray.full ( &( "stack" ) ) top reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 := 
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) reduced 0) = (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (top <> 0)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (0 <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced)))) (PreH11 : (0 <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves ) ))) (PreH14 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) (PreH15 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) top reduced )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "moves" ) )) # Int  |-> moves)
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
|--
  “ ((top - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top - 1 )) ”
.

Definition solver_safety_wit_7 := 
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) reduced 0) = (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (top <> 0)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (0 <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced)))) (PreH11 : (0 <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves ) ))) (PreH14 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) (PreH15 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) top reduced )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> (top - 1 ))
  **  ((( &( "moves" ) )) # Int  |-> moves)
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
|--
  “ ((moves + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (moves + 1 )) ”
.

Definition solver_safety_wit_8 := 
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : (top = 0)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced)))) (PreH10 : (0 <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves ) ))) (PreH13 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) (PreH14 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full ( &( "stack" ) ) (top + 1 ) (app (reduced) ((cons ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "stack" ) ) (top + 1 ) 100005 )
  **  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "moves" ) )) # Int  |-> moves)
|--
  “ ((top + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top + 1 )) ”
.

Definition solver_safety_wit_9 := 
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) reduced 0) <> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (top <> 0)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (0 <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced)))) (PreH11 : (0 <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves ) ))) (PreH14 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) (PreH15 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full ( &( "stack" ) ) (top + 1 ) (app (reduced) ((cons ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "stack" ) ) (top + 1 ) 100005 )
  **  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "moves" ) )) # Int  |-> moves)
|--
  “ ((top + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top + 1 )) ”
.

Definition solver_safety_wit_10 := 
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) reduced 0) = (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (top <> 0)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (0 <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced)))) (PreH11 : (0 <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves ) ))) (PreH14 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) (PreH15 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) top reduced )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> (top - 1 ))
  **  ((( &( "moves" ) )) # Int  |-> (moves + 1 ))
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : (top = 0)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced)))) (PreH10 : (0 <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves ) ))) (PreH13 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) (PreH14 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full ( &( "stack" ) ) (top + 1 ) (app (reduced) ((cons ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "stack" ) ) (top + 1 ) 100005 )
  **  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> (top + 1 ))
  **  ((( &( "moves" ) )) # Int  |-> moves)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_12 := 
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) reduced 0) <> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (top <> 0)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (0 <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced)))) (PreH11 : (0 <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves ) ))) (PreH14 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) (PreH15 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full ( &( "stack" ) ) (top + 1 ) (app (reduced) ((cons ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "stack" ) ) (top + 1 ) 100005 )
  **  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> (top + 1 ))
  **  ((( &( "moves" ) )) # Int  |-> moves)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_13 := 
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH4 : (0 <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (0 <= top)) (PreH7 : (top <= i)) (PreH8 : (top = (Zlength (reduced)))) (PreH9 : (0 <= moves)) (PreH10 : (moves <= i)) (PreH11 : (i = (top + (2 * moves ) ))) (PreH12 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) (PreH13 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "moves" ) )) # Int  |-> moves)
  **  (CharArray.full ( &( "stack" ) ) top reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 := 
(
forall (s_pre: Z) (text: (@list Z)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full ( &( "stack" ) ) 100005 )
|--
  EX (reduced: (@list Z)) ,
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 100000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength (text))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (Zlength (reduced))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (0 + (2 * 0 ) )) ” 
  &&  “ (PrefixGameState (sublist (0) (0) (text)) reduced 0 ) ”
  &&  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) 0 reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) 0 100005 )
) \/
(
forall (text: (@list Z)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) ,
  TT && emp 
|--
  “ (PrefixGameState (sublist (0) (0) (text)) (@nil Z) 0 ) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (text: (@list Z)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) ,
  (PrefixGameState (sublist (0) (0) (text)) (@nil Z) 0 )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (text: (@list Z)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) ,
  (0 = (Zlength ((@nil Z))))
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (text: (@list Z)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) ,
  forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))
.

Definition solver_entail_wit_2_1 := 
(
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced_2: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) reduced_2 0) = (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (top <> 0)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (0 <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced_2)))) (PreH11 : (0 <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves ) ))) (PreH14 : (PrefixGameState (sublist (0) (i) (text)) reduced_2 moves )) (PreH15 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) top reduced_2 )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
|--
  EX (reduced: (@list Z)) ,
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 100000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (text))) ” 
  &&  “ (0 <= (top - 1 )) ” 
  &&  “ ((top - 1 ) <= (i + 1 )) ” 
  &&  “ ((top - 1 ) = (Zlength (reduced))) ” 
  &&  “ (0 <= (moves + 1 )) ” 
  &&  “ ((moves + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) = ((top - 1 ) + (2 * (moves + 1 ) ) )) ” 
  &&  “ (PrefixGameState (sublist (0) ((i + 1 )) (text)) reduced (moves + 1 ) ) ”
  &&  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) (top - 1 ) reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) (top - 1 ) 100005 )
) \/
(
forall (text: (@list Z)) (moves: Z) (reduced_2: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) reduced_2 0) = (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (top <> 0)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (0 <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced_2)))) (PreH11 : (0 <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves ) ))) (PreH14 : (PrefixGameState (sublist (0) (i) (text)) reduced_2 moves )) (PreH15 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full ( &( "stack" ) ) top reduced_2 )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
|--
  EX (reduced: (@list Z)) ,
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 100000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (text))) ” 
  &&  “ (0 <= (top - 1 )) ” 
  &&  “ ((top - 1 ) <= (i + 1 )) ” 
  &&  “ ((top - 1 ) = (Zlength (reduced))) ” 
  &&  “ (0 <= (moves + 1 )) ” 
  &&  “ ((moves + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) = ((top - 1 ) + (2 * (moves + 1 ) ) )) ” 
  &&  “ (PrefixGameState (sublist (0) ((i + 1 )) (text)) reduced (moves + 1 ) ) ”
  &&  (CharArray.full ( &( "stack" ) ) (top - 1 ) reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) (top - 1 ) 100005 )
).

Definition solver_entail_wit_2_2 := 
(
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced_2: (@list Z)) (top: Z) (i: Z) (PreH1 : (top = 0)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced_2)))) (PreH10 : (0 <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves ) ))) (PreH13 : (PrefixGameState (sublist (0) (i) (text)) reduced_2 moves )) (PreH14 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full ( &( "stack" ) ) (top + 1 ) (app (reduced_2) ((cons ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "stack" ) ) (top + 1 ) 100005 )
  **  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  EX (reduced: (@list Z)) ,
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 100000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (text))) ” 
  &&  “ (0 <= (top + 1 )) ” 
  &&  “ ((top + 1 ) <= (i + 1 )) ” 
  &&  “ ((top + 1 ) = (Zlength (reduced))) ” 
  &&  “ (0 <= moves) ” 
  &&  “ (moves <= (i + 1 )) ” 
  &&  “ ((i + 1 ) = ((top + 1 ) + (2 * moves ) )) ” 
  &&  “ (PrefixGameState (sublist (0) ((i + 1 )) (text)) reduced moves ) ”
  &&  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) (top + 1 ) reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) (top + 1 ) 100005 )
) \/
(
forall (text: (@list Z)) (moves: Z) (reduced_2: (@list Z)) (top: Z) (i: Z) (PreH1 : (top = 0)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced_2)))) (PreH10 : (0 <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves ) ))) (PreH13 : (PrefixGameState (sublist (0) (i) (text)) reduced_2 moves )) (PreH14 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  TT && emp 
|--
  “ (PrefixGameState (sublist (0) (((top + (2 * moves ) ) + 1 )) (text)) (app (reduced_2) ((cons ((Znth (top + (2 * moves ) ) (app (text) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) moves ) ” 
  &&  “ ((0 + 1 ) = (Zlength ((app (reduced_2) ((cons ((Znth (top + (2 * moves ) ) (app (text) ((cons (0) ((@nil Z))))) 0)) ((@nil Z)))))))) ” 
  &&  “ (((top + (2 * moves ) ) + 1 ) <= (Zlength (text))) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 := 
forall (text: (@list Z)) (moves: Z) (reduced_2: (@list Z)) (top: Z) (i: Z) (PreH1 : (top = 0)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced_2)))) (PreH10 : (0 <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves ) ))) (PreH13 : (PrefixGameState (sublist (0) (i) (text)) reduced_2 moves )) (PreH14 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (PrefixGameState (sublist (0) (((top + (2 * moves ) ) + 1 )) (text)) (app (reduced_2) ((cons ((Znth (top + (2 * moves ) ) (app (text) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) moves )
.

Definition solver_entail_wit_2_2_split_goal_2 := 
forall (text: (@list Z)) (moves: Z) (reduced_2: (@list Z)) (top: Z) (i: Z) (PreH1 : (top = 0)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced_2)))) (PreH10 : (0 <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves ) ))) (PreH13 : (PrefixGameState (sublist (0) (i) (text)) reduced_2 moves )) (PreH14 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  ((0 + 1 ) = (Zlength ((app (reduced_2) ((cons ((Znth (top + (2 * moves ) ) (app (text) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))))))
.

Definition solver_entail_wit_2_2_split_goal_3 := 
forall (text: (@list Z)) (moves: Z) (reduced_2: (@list Z)) (top: Z) (i: Z) (PreH1 : (top = 0)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced_2)))) (PreH10 : (0 <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves ) ))) (PreH13 : (PrefixGameState (sublist (0) (i) (text)) reduced_2 moves )) (PreH14 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (((top + (2 * moves ) ) + 1 ) <= (Zlength (text)))
.

Definition solver_entail_wit_2_3 := 
(
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced_2: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) reduced_2 0) <> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (top <> 0)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (0 <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced_2)))) (PreH11 : (0 <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves ) ))) (PreH14 : (PrefixGameState (sublist (0) (i) (text)) reduced_2 moves )) (PreH15 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full ( &( "stack" ) ) (top + 1 ) (app (reduced_2) ((cons ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "stack" ) ) (top + 1 ) 100005 )
  **  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  EX (reduced: (@list Z)) ,
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 100000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (text))) ” 
  &&  “ (0 <= (top + 1 )) ” 
  &&  “ ((top + 1 ) <= (i + 1 )) ” 
  &&  “ ((top + 1 ) = (Zlength (reduced))) ” 
  &&  “ (0 <= moves) ” 
  &&  “ (moves <= (i + 1 )) ” 
  &&  “ ((i + 1 ) = ((top + 1 ) + (2 * moves ) )) ” 
  &&  “ (PrefixGameState (sublist (0) ((i + 1 )) (text)) reduced moves ) ”
  &&  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) (top + 1 ) reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) (top + 1 ) 100005 )
) \/
(
forall (text: (@list Z)) (moves: Z) (reduced_2: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) reduced_2 0) <> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (top <> 0)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (0 <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced_2)))) (PreH11 : (0 <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves ) ))) (PreH14 : (PrefixGameState (sublist (0) (i) (text)) reduced_2 moves )) (PreH15 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  TT && emp 
|--
  “ (PrefixGameState (sublist (0) (((top + (2 * moves ) ) + 1 )) (text)) (app (reduced_2) ((cons ((Znth (top + (2 * moves ) ) (app (text) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) moves ) ” 
  &&  “ ((top + 1 ) = (Zlength ((app (reduced_2) ((cons ((Znth (top + (2 * moves ) ) (app (text) ((cons (0) ((@nil Z))))) 0)) ((@nil Z)))))))) ” 
  &&  “ (((top + (2 * moves ) ) + 1 ) <= (Zlength (text))) ”
  &&  emp
).

Definition solver_entail_wit_2_3_split_goal_1 := 
forall (text: (@list Z)) (moves: Z) (reduced_2: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) reduced_2 0) <> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (top <> 0)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (0 <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced_2)))) (PreH11 : (0 <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves ) ))) (PreH14 : (PrefixGameState (sublist (0) (i) (text)) reduced_2 moves )) (PreH15 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (PrefixGameState (sublist (0) (((top + (2 * moves ) ) + 1 )) (text)) (app (reduced_2) ((cons ((Znth (top + (2 * moves ) ) (app (text) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))) moves )
.

Definition solver_entail_wit_2_3_split_goal_2 := 
forall (text: (@list Z)) (moves: Z) (reduced_2: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) reduced_2 0) <> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (top <> 0)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (0 <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced_2)))) (PreH11 : (0 <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves ) ))) (PreH14 : (PrefixGameState (sublist (0) (i) (text)) reduced_2 moves )) (PreH15 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  ((top + 1 ) = (Zlength ((app (reduced_2) ((cons ((Znth (top + (2 * moves ) ) (app (text) ((cons (0) ((@nil Z))))) 0)) ((@nil Z))))))))
.

Definition solver_entail_wit_2_3_split_goal_3 := 
forall (text: (@list Z)) (moves: Z) (reduced_2: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) reduced_2 0) <> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (top <> 0)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (0 <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced_2)))) (PreH11 : (0 <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves ) ))) (PreH14 : (PrefixGameState (sublist (0) (i) (text)) reduced_2 moves )) (PreH15 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (((top + (2 * moves ) ) + 1 ) <= (Zlength (text)))
.

Definition solver_return_wit_1 := 
(
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH4 : (0 <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (0 <= top)) (PreH7 : (top <= i)) (PreH8 : (top = (Zlength (reduced)))) (PreH9 : (0 <= moves)) (PreH10 : (moves <= i)) (PreH11 : (i = (top + (2 * moves ) ))) (PreH12 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) (PreH13 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) top reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
|--
  “ (Spec text (Z.land moves 1) ) ”
  &&  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_full ( &( "stack" ) ) 100005 )
) \/
(
forall (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH4 : (0 <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (0 <= top)) (PreH7 : (top <= i)) (PreH8 : (top = (Zlength (reduced)))) (PreH9 : (0 <= moves)) (PreH10 : (moves <= i)) (PreH11 : (i = (top + (2 * moves ) ))) (PreH12 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) (PreH13 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 0)) ,
  (CharArray.full ( &( "stack" ) ) top reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
|--
  “ (Spec text (Z.land moves 1) ) ”
  &&  (CharArray.undef_full ( &( "stack" ) ) 100005 )
).

Definition solver_return_wit_1_split_goal_1 := 
forall (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH4 : (0 <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (0 <= top)) (PreH7 : (top <= i)) (PreH8 : (top = (Zlength (reduced)))) (PreH9 : (0 <= moves)) (PreH10 : (moves <= i)) (PreH11 : (i = (top + (2 * moves ) ))) (PreH12 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) (PreH13 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 0)) ,
  (CharArray.full ( &( "stack" ) ) top reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
|--
  “ (Spec text (Z.land moves 1) ) ”
.

Definition solver_return_wit_1_split_goal_spatial := 
forall (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH4 : (0 <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (0 <= top)) (PreH7 : (top <= i)) (PreH8 : (top = (Zlength (reduced)))) (PreH9 : (0 <= moves)) (PreH10 : (moves <= i)) (PreH11 : (i = (top + (2 * moves ) ))) (PreH12 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) (PreH13 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 0)) ,
  (CharArray.full ( &( "stack" ) ) top reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
|--
  (CharArray.undef_full ( &( "stack" ) ) 100005 )
.

Definition solver_partial_solve_wit_1 := 
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100000)) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH4 : (0 <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (0 <= top)) (PreH7 : (top <= i)) (PreH8 : (top = (Zlength (reduced)))) (PreH9 : (0 <= moves)) (PreH10 : (moves <= i)) (PreH11 : (i = (top + (2 * moves ) ))) (PreH12 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) top reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
|--
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 100000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (text))) ” 
  &&  “ (0 <= top) ” 
  &&  “ (top <= i) ” 
  &&  “ (top = (Zlength (reduced))) ” 
  &&  “ (0 <= moves) ” 
  &&  “ (moves <= i) ” 
  &&  “ (i = (top + (2 * moves ) )) ” 
  &&  “ (PrefixGameState (sublist (0) (i) (text)) reduced moves ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) top reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
.

Definition solver_partial_solve_wit_2 := 
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : (top <> 0)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced)))) (PreH10 : (0 <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves ) ))) (PreH13 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) (PreH14 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) top reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
|--
  “ (top <> 0) ” 
  &&  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 100000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (text))) ” 
  &&  “ (0 <= top) ” 
  &&  “ (top <= i) ” 
  &&  “ (top = (Zlength (reduced))) ” 
  &&  “ (0 <= moves) ” 
  &&  “ (moves <= i) ” 
  &&  “ (i = (top + (2 * moves ) )) ” 
  &&  “ (PrefixGameState (sublist (0) (i) (text)) reduced moves ) ” 
  &&  “ ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((( &( "stack" ) ) + ((top - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (top - 1 ) reduced 0))
  **  (CharArray.missing_i ( &( "stack" ) ) (top - 1 ) 0 top reduced )
  **  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
.

Definition solver_partial_solve_wit_3 := 
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : (top <> 0)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced)))) (PreH10 : (0 <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves ) ))) (PreH13 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) (PreH14 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full ( &( "stack" ) ) top reduced )
  **  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
|--
  “ (top <> 0) ” 
  &&  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 100000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (text))) ” 
  &&  “ (0 <= top) ” 
  &&  “ (top <= i) ” 
  &&  “ (top = (Zlength (reduced))) ” 
  &&  “ (0 <= moves) ” 
  &&  “ (moves <= i) ” 
  &&  “ (i = (top + (2 * moves ) )) ” 
  &&  “ (PrefixGameState (sublist (0) (i) (text)) reduced moves ) ” 
  &&  “ ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) top reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
.

Definition solver_partial_solve_wit_4 := 
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : (top = 0)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced)))) (PreH10 : (0 <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves ) ))) (PreH13 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) (PreH14 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) top reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
|--
  “ (top = 0) ” 
  &&  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 100000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (text))) ” 
  &&  “ (0 <= top) ” 
  &&  “ (top <= i) ” 
  &&  “ (top = (Zlength (reduced))) ” 
  &&  “ (0 <= moves) ” 
  &&  “ (moves <= i) ” 
  &&  “ (i = (top + (2 * moves ) )) ” 
  &&  “ (PrefixGameState (sublist (0) (i) (text)) reduced moves ) ” 
  &&  “ ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) top reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
.

Definition solver_partial_solve_wit_5 := 
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : (top = 0)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100000)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= top)) (PreH8 : (top <= i)) (PreH9 : (top = (Zlength (reduced)))) (PreH10 : (0 <= moves)) (PreH11 : (moves <= i)) (PreH12 : (i = (top + (2 * moves ) ))) (PreH13 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) (PreH14 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) top reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
|--
  “ (top = 0) ” 
  &&  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 100000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (text))) ” 
  &&  “ (0 <= top) ” 
  &&  “ (top <= i) ” 
  &&  “ (top = (Zlength (reduced))) ” 
  &&  “ (0 <= moves) ” 
  &&  “ (moves <= i) ” 
  &&  “ (i = (top + (2 * moves ) )) ” 
  &&  “ (PrefixGameState (sublist (0) (i) (text)) reduced moves ) ” 
  &&  “ ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((( &( "stack" ) ) + (top * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg ( &( "stack" ) ) (top + 1 ) 100005 )
  **  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) top reduced )
.

Definition solver_partial_solve_wit_6 := 
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) reduced 0) <> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (top <> 0)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (0 <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced)))) (PreH11 : (0 <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves ) ))) (PreH14 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) (PreH15 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) top reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
|--
  “ ((Znth (top - 1 ) reduced 0) <> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0)) ” 
  &&  “ (top <> 0) ” 
  &&  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 100000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (text))) ” 
  &&  “ (0 <= top) ” 
  &&  “ (top <= i) ” 
  &&  “ (top = (Zlength (reduced))) ” 
  &&  “ (0 <= moves) ” 
  &&  “ (moves <= i) ” 
  &&  “ (i = (top + (2 * moves ) )) ” 
  &&  “ (PrefixGameState (sublist (0) (i) (text)) reduced moves ) ” 
  &&  “ ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) top reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
.

Definition solver_partial_solve_wit_7 := 
forall (s_pre: Z) (text: (@list Z)) (moves: Z) (reduced: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) reduced 0) <> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (top <> 0)) (PreH3 : (1 <= (Zlength (text)))) (PreH4 : ((Zlength (text)) <= 100000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= (Zlength (text)))) (PreH8 : (0 <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (reduced)))) (PreH11 : (0 <= moves)) (PreH12 : (moves <= i)) (PreH13 : (i = (top + (2 * moves ) ))) (PreH14 : (PrefixGameState (sublist (0) (i) (text)) reduced moves )) (PreH15 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) top reduced )
  **  (CharArray.undef_seg ( &( "stack" ) ) top 100005 )
|--
  “ ((Znth (top - 1 ) reduced 0) <> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0)) ” 
  &&  “ (top <> 0) ” 
  &&  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 100000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (text))) ” 
  &&  “ (0 <= top) ” 
  &&  “ (top <= i) ” 
  &&  “ (top = (Zlength (reduced))) ” 
  &&  “ (0 <= moves) ” 
  &&  “ (moves <= i) ” 
  &&  “ (i = (top + (2 * moves ) )) ” 
  &&  “ (PrefixGameState (sublist (0) (i) (text)) reduced moves ) ” 
  &&  “ ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((( &( "stack" ) ) + (top * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg ( &( "stack" ) ) (top + 1 ) 100005 )
  **  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full ( &( "stack" ) ) top reduced )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.

End VC_Correct.
