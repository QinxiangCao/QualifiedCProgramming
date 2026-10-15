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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P016_450A_jzzhu_and_children_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (wants_pre: Z) (wants_data: (@list Z)) (PreH1 : (1 <= (Zlength (wants_data)))) (PreH2 : ((Zlength (wants_data)) <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (wants_data)))) -> ((1 <= (Znth i wants_data 0)) /\ ((Znth i wants_data 0) <= 100)))) (PreH6 : (n_pre = (Zlength (wants_data)))) ,
  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "answer" ) )) # Int  |-> 1)
  **  ((( &( "wants" ) )) # Ptr  |-> wants_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full wants_pre n_pre wants_data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (wants_pre: Z) (wants_data: (@list Z)) (PreH1 : (1 <= (Zlength (wants_data)))) (PreH2 : ((Zlength (wants_data)) <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (wants_data)))) -> ((1 <= (Znth i wants_data 0)) /\ ((Znth i wants_data 0) <= 100)))) (PreH6 : (n_pre = (Zlength (wants_data)))) ,
  ((( &( "answer" ) )) # Int  |->_)
  **  ((( &( "wants" ) )) # Ptr  |-> wants_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full wants_pre n_pre wants_data )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_3 := 
forall (m_pre: Z) (n_pre: Z) (wants_pre: Z) (wants_data: (@list Z)) (PreH1 : (1 <= (Zlength (wants_data)))) (PreH2 : ((Zlength (wants_data)) <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (wants_data)))) -> ((1 <= (Znth i wants_data 0)) /\ ((Znth i wants_data 0) <= 100)))) (PreH6 : (n_pre = (Zlength (wants_data)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |-> 0)
  **  ((( &( "answer" ) )) # Int  |-> 1)
  **  ((( &( "wants" ) )) # Ptr  |-> wants_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full wants_pre n_pre wants_data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (m_pre: Z) (n_pre: Z) (wants_pre: Z) (wants_data: (@list Z)) (best: Z) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= (Zlength (wants_data)))) (PreH3 : ((Zlength (wants_data)) <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100)))) (PreH7 : (n_pre = (Zlength (wants_data)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (LastMaxPrefix m_pre wants_data i best answer )) ,
  (IntArray.full wants_pre n_pre wants_data )
  **  ((( &( "turns" ) )) # Int  |->_)
  **  ((( &( "wants" ) )) # Ptr  |-> wants_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((((Znth i wants_data 0) + m_pre ) - 1 ) <> (INT_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_5 := 
forall (m_pre: Z) (n_pre: Z) (wants_pre: Z) (wants_data: (@list Z)) (best: Z) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= (Zlength (wants_data)))) (PreH3 : ((Zlength (wants_data)) <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100)))) (PreH7 : (n_pre = (Zlength (wants_data)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (LastMaxPrefix m_pre wants_data i best answer )) ,
  (IntArray.full wants_pre n_pre wants_data )
  **  ((( &( "turns" ) )) # Int  |->_)
  **  ((( &( "wants" ) )) # Ptr  |-> wants_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((((Znth i wants_data 0) + m_pre ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i wants_data 0) + m_pre ) - 1 )) ”
.

Definition solver_safety_wit_6 := 
forall (m_pre: Z) (n_pre: Z) (wants_pre: Z) (wants_data: (@list Z)) (best: Z) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= (Zlength (wants_data)))) (PreH3 : ((Zlength (wants_data)) <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100)))) (PreH7 : (n_pre = (Zlength (wants_data)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (LastMaxPrefix m_pre wants_data i best answer )) ,
  (IntArray.full wants_pre n_pre wants_data )
  **  ((( &( "turns" ) )) # Int  |->_)
  **  ((( &( "wants" ) )) # Ptr  |-> wants_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (((Znth i wants_data 0) + m_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i wants_data 0) + m_pre )) ”
.

Definition solver_safety_wit_7 := 
forall (m_pre: Z) (n_pre: Z) (wants_pre: Z) (wants_data: (@list Z)) (best: Z) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= (Zlength (wants_data)))) (PreH3 : ((Zlength (wants_data)) <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100)))) (PreH7 : (n_pre = (Zlength (wants_data)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (LastMaxPrefix m_pre wants_data i best answer )) ,
  (IntArray.full wants_pre n_pre wants_data )
  **  ((( &( "turns" ) )) # Int  |->_)
  **  ((( &( "wants" ) )) # Ptr  |-> wants_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_8 := 
forall (m_pre: Z) (n_pre: Z) (wants_pre: Z) (wants_data: (@list Z)) (best: Z) (answer: Z) (i: Z) (PreH1 : (((((Znth i wants_data 0) + m_pre ) - 1 ) ÷ m_pre ) >= best)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (wants_data)))) (PreH4 : ((Zlength (wants_data)) <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100)))) (PreH8 : (n_pre = (Zlength (wants_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (LastMaxPrefix m_pre wants_data i best answer )) ,
  (IntArray.full wants_pre n_pre wants_data )
  **  ((( &( "turns" ) )) # Int  |-> ((((Znth i wants_data 0) + m_pre ) - 1 ) ÷ m_pre ))
  **  ((( &( "wants" ) )) # Ptr  |-> wants_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "best" ) )) # Int  |-> ((((Znth i wants_data 0) + m_pre ) - 1 ) ÷ m_pre ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_9 := 
forall (m_pre: Z) (n_pre: Z) (wants_pre: Z) (wants_data: (@list Z)) (best: Z) (answer: Z) (i: Z) (PreH1 : (((((Znth i wants_data 0) + m_pre ) - 1 ) ÷ m_pre ) >= best)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (wants_data)))) (PreH4 : ((Zlength (wants_data)) <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100)))) (PreH8 : (n_pre = (Zlength (wants_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (LastMaxPrefix m_pre wants_data i best answer )) ,
  (IntArray.full wants_pre n_pre wants_data )
  **  ((( &( "turns" ) )) # Int  |-> ((((Znth i wants_data 0) + m_pre ) - 1 ) ÷ m_pre ))
  **  ((( &( "wants" ) )) # Ptr  |-> wants_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "best" ) )) # Int  |-> ((((Znth i wants_data 0) + m_pre ) - 1 ) ÷ m_pre ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 := 
forall (m_pre: Z) (n_pre: Z) (wants_pre: Z) (wants_data: (@list Z)) (best: Z) (answer: Z) (i: Z) (PreH1 : (((((Znth i wants_data 0) + m_pre ) - 1 ) ÷ m_pre ) >= best)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (wants_data)))) (PreH4 : ((Zlength (wants_data)) <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100)))) (PreH8 : (n_pre = (Zlength (wants_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (LastMaxPrefix m_pre wants_data i best answer )) ,
  (IntArray.full wants_pre n_pre wants_data )
  **  ((( &( "wants" ) )) # Ptr  |-> wants_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "best" ) )) # Int  |-> ((((Znth i wants_data 0) + m_pre ) - 1 ) ÷ m_pre ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (m_pre: Z) (n_pre: Z) (wants_pre: Z) (wants_data: (@list Z)) (best: Z) (answer: Z) (i: Z) (PreH1 : (((((Znth i wants_data 0) + m_pre ) - 1 ) ÷ m_pre ) < best)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (wants_data)))) (PreH4 : ((Zlength (wants_data)) <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100)))) (PreH8 : (n_pre = (Zlength (wants_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (LastMaxPrefix m_pre wants_data i best answer )) ,
  (IntArray.full wants_pre n_pre wants_data )
  **  ((( &( "wants" ) )) # Ptr  |-> wants_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (m_pre: Z) (n_pre: Z) (wants_pre: Z) (wants_data: (@list Z)) (PreH1 : (1 <= (Zlength (wants_data)))) (PreH2 : ((Zlength (wants_data)) <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (wants_data)))) -> ((1 <= (Znth i wants_data 0)) /\ ((Znth i wants_data 0) <= 100)))) (PreH6 : (n_pre = (Zlength (wants_data)))) ,
  (IntArray.full wants_pre n_pre wants_data )
|--
  “ (1 <= (Zlength (wants_data))) ” 
  &&  “ ((Zlength (wants_data)) <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100))) ” 
  &&  “ (n_pre = (Zlength (wants_data))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (LastMaxPrefix m_pre wants_data 0 0 1 ) ”
  &&  (IntArray.full wants_pre n_pre wants_data )
) \/
(
forall (m_pre: Z) (n_pre: Z) (wants_data: (@list Z)) (PreH1 : (1 <= (Zlength (wants_data)))) (PreH2 : ((Zlength (wants_data)) <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (wants_data)))) -> ((1 <= (Znth i wants_data 0)) /\ ((Znth i wants_data 0) <= 100)))) (PreH6 : (n_pre = (Zlength (wants_data)))) ,
  TT && emp 
|--
  “ (LastMaxPrefix m_pre wants_data 0 0 1 ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (wants_data: (@list Z)) (PreH1 : (1 <= (Zlength (wants_data)))) (PreH2 : ((Zlength (wants_data)) <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (wants_data)))) -> ((1 <= (Znth i wants_data 0)) /\ ((Znth i wants_data 0) <= 100)))) (PreH6 : (n_pre = (Zlength (wants_data)))) ,
  (LastMaxPrefix m_pre wants_data 0 0 1 )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (wants_data: (@list Z)) (PreH1 : (1 <= (Zlength (wants_data)))) (PreH2 : ((Zlength (wants_data)) <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (wants_data)))) -> ((1 <= (Znth i wants_data 0)) /\ ((Znth i wants_data 0) <= 100)))) (PreH6 : (n_pre = (Zlength (wants_data)))) ,
  forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100)))
.

Definition solver_entail_wit_2_1 := 
(
forall (m_pre: Z) (n_pre: Z) (wants_pre: Z) (wants_data: (@list Z)) (best: Z) (answer: Z) (i: Z) (PreH1 : (((((Znth i wants_data 0) + m_pre ) - 1 ) ÷ m_pre ) >= best)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (wants_data)))) (PreH4 : ((Zlength (wants_data)) <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100)))) (PreH8 : (n_pre = (Zlength (wants_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (LastMaxPrefix m_pre wants_data i best answer )) ,
  (IntArray.full wants_pre n_pre wants_data )
|--
  “ (1 <= (Zlength (wants_data))) ” 
  &&  “ ((Zlength (wants_data)) <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100))) ” 
  &&  “ (n_pre = (Zlength (wants_data))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (LastMaxPrefix m_pre wants_data (i + 1 ) ((((Znth i wants_data 0) + m_pre ) - 1 ) ÷ m_pre ) (i + 1 ) ) ”
  &&  (IntArray.full wants_pre n_pre wants_data )
) \/
(
forall (m_pre: Z) (n_pre: Z) (wants_data: (@list Z)) (best: Z) (answer: Z) (i: Z) (PreH1 : (((((Znth i wants_data 0) + m_pre ) - 1 ) ÷ m_pre ) >= best)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (wants_data)))) (PreH4 : ((Zlength (wants_data)) <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100)))) (PreH8 : (n_pre = (Zlength (wants_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (LastMaxPrefix m_pre wants_data i best answer )) ,
  TT && emp 
|--
  “ (LastMaxPrefix m_pre wants_data (i + 1 ) ((((Znth i wants_data 0) + m_pre ) - 1 ) ÷ m_pre ) (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (wants_data: (@list Z)) (best: Z) (answer: Z) (i: Z) (PreH1 : (((((Znth i wants_data 0) + m_pre ) - 1 ) ÷ m_pre ) >= best)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (wants_data)))) (PreH4 : ((Zlength (wants_data)) <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100)))) (PreH8 : (n_pre = (Zlength (wants_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (LastMaxPrefix m_pre wants_data i best answer )) ,
  (LastMaxPrefix m_pre wants_data (i + 1 ) ((((Znth i wants_data 0) + m_pre ) - 1 ) ÷ m_pre ) (i + 1 ) )
.

Definition solver_entail_wit_2_2 := 
(
forall (m_pre: Z) (n_pre: Z) (wants_pre: Z) (wants_data: (@list Z)) (best: Z) (answer: Z) (i: Z) (PreH1 : (((((Znth i wants_data 0) + m_pre ) - 1 ) ÷ m_pre ) < best)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (wants_data)))) (PreH4 : ((Zlength (wants_data)) <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100)))) (PreH8 : (n_pre = (Zlength (wants_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (LastMaxPrefix m_pre wants_data i best answer )) ,
  (IntArray.full wants_pre n_pre wants_data )
|--
  “ (1 <= (Zlength (wants_data))) ” 
  &&  “ ((Zlength (wants_data)) <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100))) ” 
  &&  “ (n_pre = (Zlength (wants_data))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (LastMaxPrefix m_pre wants_data (i + 1 ) best answer ) ”
  &&  (IntArray.full wants_pre n_pre wants_data )
) \/
(
forall (m_pre: Z) (n_pre: Z) (wants_data: (@list Z)) (best: Z) (answer: Z) (i: Z) (PreH1 : (((((Znth i wants_data 0) + m_pre ) - 1 ) ÷ m_pre ) < best)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (wants_data)))) (PreH4 : ((Zlength (wants_data)) <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100)))) (PreH8 : (n_pre = (Zlength (wants_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (LastMaxPrefix m_pre wants_data i best answer )) ,
  TT && emp 
|--
  “ (LastMaxPrefix m_pre wants_data (i + 1 ) best answer ) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (wants_data: (@list Z)) (best: Z) (answer: Z) (i: Z) (PreH1 : (((((Znth i wants_data 0) + m_pre ) - 1 ) ÷ m_pre ) < best)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (wants_data)))) (PreH4 : ((Zlength (wants_data)) <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100)))) (PreH8 : (n_pre = (Zlength (wants_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (LastMaxPrefix m_pre wants_data i best answer )) ,
  (LastMaxPrefix m_pre wants_data (i + 1 ) best answer )
.

Definition solver_return_wit_1 := 
(
forall (m_pre: Z) (n_pre: Z) (wants_pre: Z) (wants_data: (@list Z)) (best: Z) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= (Zlength (wants_data)))) (PreH3 : ((Zlength (wants_data)) <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100)))) (PreH7 : (n_pre = (Zlength (wants_data)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (LastMaxPrefix m_pre wants_data i best answer )) ,
  (IntArray.full wants_pre n_pre wants_data )
|--
  “ (Spec m_pre wants_data answer ) ”
  &&  (IntArray.full wants_pre n_pre wants_data )
) \/
(
forall (m_pre: Z) (n_pre: Z) (wants_data: (@list Z)) (best: Z) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= (Zlength (wants_data)))) (PreH3 : ((Zlength (wants_data)) <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100)))) (PreH7 : (n_pre = (Zlength (wants_data)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (LastMaxPrefix m_pre wants_data i best answer )) ,
  TT && emp 
|--
  “ (Spec m_pre wants_data answer ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (wants_data: (@list Z)) (best: Z) (answer: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= (Zlength (wants_data)))) (PreH3 : ((Zlength (wants_data)) <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100)))) (PreH7 : (n_pre = (Zlength (wants_data)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (LastMaxPrefix m_pre wants_data i best answer )) ,
  (Spec m_pre wants_data answer )
.

Definition solver_partial_solve_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (wants_pre: Z) (wants_data: (@list Z)) (best: Z) (answer: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= (Zlength (wants_data)))) (PreH3 : ((Zlength (wants_data)) <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100)))) (PreH7 : (n_pre = (Zlength (wants_data)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (LastMaxPrefix m_pre wants_data i best answer )) ,
  (IntArray.full wants_pre n_pre wants_data )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= (Zlength (wants_data))) ” 
  &&  “ ((Zlength (wants_data)) <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (wants_data)))) -> ((1 <= (Znth j wants_data 0)) /\ ((Znth j wants_data 0) <= 100))) ” 
  &&  “ (n_pre = (Zlength (wants_data))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (LastMaxPrefix m_pre wants_data i best answer ) ”
  &&  (((wants_pre + (i * sizeof(INT)))) # Int  |-> (Znth i wants_data 0))
  **  (IntArray.missing_i wants_pre i 0 n_pre wants_data )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.

End VC_Correct.
