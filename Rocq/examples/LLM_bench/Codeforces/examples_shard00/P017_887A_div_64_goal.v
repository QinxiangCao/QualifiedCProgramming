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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P017_887A_div_64_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (s_pre: Z) (text: (@list Z)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> (((Znth i text 0) = 48) \/ ((Znth i text 0) = 49)))) ,
  ((( &( "zeros" ) )) # Int  |->_)
  **  ((( &( "seen_one" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (s_pre: Z) (text: (@list Z)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> (((Znth i text 0) = 48) \/ ((Znth i text 0) = 49)))) ,
  ((( &( "seen_one" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (s_pre: Z) (text: (@list Z)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> (((Znth i text 0) = 48) \/ ((Znth i text 0) = 49)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "zeros" ) )) # Int  |-> 0)
  **  ((( &( "seen_one" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (s_pre: Z) (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100)) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH4 : (0 <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (0 <= seen_one)) (PreH7 : (seen_one <= 1)) (PreH8 : (0 <= zeros)) (PreH9 : (zeros <= i)) (PreH10 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH11 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "seen_one" ) )) # Int  |-> seen_one)
  **  ((( &( "zeros" ) )) # Int  |-> zeros)
|--
  “ (49 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_5 := 
forall (s_pre: Z) (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "seen_one" ) )) # Int  |-> seen_one)
  **  ((( &( "zeros" ) )) # Int  |-> zeros)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 := 
forall (s_pre: Z) (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH13 : (seen_one <> 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "seen_one" ) )) # Int  |-> seen_one)
  **  ((( &( "zeros" ) )) # Int  |-> zeros)
|--
  “ ((zeros + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (zeros + 1 )) ”
.

Definition solver_safety_wit_7 := 
forall (s_pre: Z) (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "seen_one" ) )) # Int  |-> 1)
  **  ((( &( "zeros" ) )) # Int  |-> zeros)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_8 := 
forall (s_pre: Z) (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH13 : (seen_one <> 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "seen_one" ) )) # Int  |-> seen_one)
  **  ((( &( "zeros" ) )) # Int  |-> (zeros + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_9 := 
forall (s_pre: Z) (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH13 : (seen_one = 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "seen_one" ) )) # Int  |-> seen_one)
  **  ((( &( "zeros" ) )) # Int  |-> zeros)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_10 := 
forall (s_pre: Z) (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100)) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH4 : (0 <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (0 <= seen_one)) (PreH7 : (seen_one <= 1)) (PreH8 : (0 <= zeros)) (PreH9 : (zeros <= i)) (PreH10 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH11 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "seen_one" ) )) # Int  |-> seen_one)
  **  ((( &( "zeros" ) )) # Int  |-> zeros)
|--
  “ (6 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 6) ”
.

Definition solver_entail_wit_1 := 
(
forall (s_pre: Z) (text: (@list Z)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> (((Znth i text 0) = 48) \/ ((Znth i text 0) = 49)))) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength (text))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (PrefixScan (sublist (0) (0) (text)) 0 0 ) ”
  &&  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> (((Znth i text 0) = 48) \/ ((Znth i text 0) = 49)))) ,
  TT && emp 
|--
  “ (PrefixScan (sublist (0) (0) (text)) 0 0 ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (text: (@list Z)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> (((Znth i text 0) = 48) \/ ((Znth i text 0) = 49)))) ,
  (PrefixScan (sublist (0) (0) (text)) 0 0 )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (text: (@list Z)) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (text)))) -> (((Znth i text 0) = 48) \/ ((Znth i text 0) = 49)))) ,
  forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))
.

Definition solver_entail_wit_2_1 := 
(
forall (s_pre: Z) (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (text))) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (0 <= zeros) ” 
  &&  “ (zeros <= (i + 1 )) ” 
  &&  “ (PrefixScan (sublist (0) ((i + 1 )) (text)) 1 zeros ) ”
  &&  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  TT && emp 
|--
  “ (PrefixScan (sublist (0) ((i + 1 )) (text)) 1 zeros ) ” 
  &&  “ ((i + 1 ) <= (Zlength (text))) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 := 
forall (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (PrefixScan (sublist (0) ((i + 1 )) (text)) 1 zeros )
.

Definition solver_entail_wit_2_1_split_goal_2 := 
forall (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  ((i + 1 ) <= (Zlength (text)))
.

Definition solver_entail_wit_2_2 := 
(
forall (s_pre: Z) (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH13 : (seen_one <> 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (text))) ” 
  &&  “ (0 <= seen_one) ” 
  &&  “ (seen_one <= 1) ” 
  &&  “ (0 <= (zeros + 1 )) ” 
  &&  “ ((zeros + 1 ) <= (i + 1 )) ” 
  &&  “ (PrefixScan (sublist (0) ((i + 1 )) (text)) seen_one (zeros + 1 ) ) ”
  &&  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH13 : (seen_one <> 0)) ,
  TT && emp 
|--
  “ (PrefixScan (sublist (0) ((i + 1 )) (text)) seen_one (zeros + 1 ) ) ” 
  &&  “ ((i + 1 ) <= (Zlength (text))) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 := 
forall (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH13 : (seen_one <> 0)) ,
  (PrefixScan (sublist (0) ((i + 1 )) (text)) seen_one (zeros + 1 ) )
.

Definition solver_entail_wit_2_2_split_goal_2 := 
forall (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH13 : (seen_one <> 0)) ,
  ((i + 1 ) <= (Zlength (text)))
.

Definition solver_entail_wit_2_3 := 
(
forall (s_pre: Z) (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH13 : (seen_one = 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (text))) ” 
  &&  “ (0 <= seen_one) ” 
  &&  “ (seen_one <= 1) ” 
  &&  “ (0 <= zeros) ” 
  &&  “ (zeros <= (i + 1 )) ” 
  &&  “ (PrefixScan (sublist (0) ((i + 1 )) (text)) seen_one zeros ) ”
  &&  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH13 : (seen_one = 0)) ,
  TT && emp 
|--
  “ (PrefixScan (sublist (0) ((i + 1 )) (text)) 0 zeros ) ” 
  &&  “ ((i + 1 ) <= (Zlength (text))) ”
  &&  emp
).

Definition solver_entail_wit_2_3_split_goal_1 := 
forall (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH13 : (seen_one = 0)) ,
  (PrefixScan (sublist (0) ((i + 1 )) (text)) 0 zeros )
.

Definition solver_entail_wit_2_3_split_goal_2 := 
forall (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH13 : (seen_one = 0)) ,
  ((i + 1 ) <= (Zlength (text)))
.

Definition solver_return_wit_1 := 
(
forall (s_pre: Z) (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : (zeros < 6)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (Spec text 0 ) ”
  &&  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : (zeros < 6)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 0)) ,
  TT && emp 
|--
  “ (Spec text 0 ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : (zeros < 6)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 0)) ,
  (Spec text 0 )
.

Definition solver_return_wit_2 := 
(
forall (s_pre: Z) (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : (zeros >= 6)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (Spec text 1 ) ”
  &&  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : (zeros >= 6)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 0)) ,
  TT && emp 
|--
  “ (Spec text 1 ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 := 
forall (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : (zeros >= 6)) (PreH2 : (1 <= (Zlength (text)))) (PreH3 : ((Zlength (text)) <= 100)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH5 : (0 <= i)) (PreH6 : (i <= (Zlength (text)))) (PreH7 : (0 <= seen_one)) (PreH8 : (seen_one <= 1)) (PreH9 : (0 <= zeros)) (PreH10 : (zeros <= i)) (PreH11 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH12 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) = 0)) ,
  (Spec text 1 )
.

Definition solver_partial_solve_wit_1 := 
forall (s_pre: Z) (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100)) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH4 : (0 <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (0 <= seen_one)) (PreH7 : (seen_one <= 1)) (PreH8 : (0 <= zeros)) (PreH9 : (zeros <= i)) (PreH10 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (text))) ” 
  &&  “ (0 <= seen_one) ” 
  &&  “ (seen_one <= 1) ” 
  &&  “ (0 <= zeros) ” 
  &&  “ (zeros <= i) ” 
  &&  “ (PrefixScan (sublist (0) (i) (text)) seen_one zeros ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_2 := 
forall (s_pre: Z) (text: (@list Z)) (zeros: Z) (seen_one: Z) (i: Z) (PreH1 : (1 <= (Zlength (text)))) (PreH2 : ((Zlength (text)) <= 100)) (PreH3 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49)))) (PreH4 : (0 <= i)) (PreH5 : (i <= (Zlength (text)))) (PreH6 : (0 <= seen_one)) (PreH7 : (seen_one <= 1)) (PreH8 : (0 <= zeros)) (PreH9 : (zeros <= i)) (PreH10 : (PrefixScan (sublist (0) (i) (text)) seen_one zeros )) (PreH11 : ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0)) ,
  (CharArray.full s_pre ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= (Zlength (text))) ” 
  &&  “ ((Zlength (text)) <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (text)))) -> (((Znth j text 0) = 48) \/ ((Znth j text 0) = 49))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (Zlength (text))) ” 
  &&  “ (0 <= seen_one) ” 
  &&  “ (seen_one <= 1) ” 
  &&  “ (0 <= zeros) ” 
  &&  “ (zeros <= i) ” 
  &&  “ (PrefixScan (sublist (0) (i) (text)) seen_one zeros ) ” 
  &&  “ ((Znth i (app (text) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (text) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 ((Zlength (text)) + 1 ) (app (text) ((cons (0) ((@nil Z))))) )
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
Axiom proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.

End VC_Correct.
