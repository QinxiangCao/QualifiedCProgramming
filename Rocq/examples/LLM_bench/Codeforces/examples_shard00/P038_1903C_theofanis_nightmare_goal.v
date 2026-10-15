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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P038_1903C_theofanis_nightmare_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> (((-100000000) <= (Znth i input 0)) /\ ((Znth i input 0) <= 100000000)))) ,
  ((( &( "answer" ) )) # Int64  |->_)
  **  ((( &( "suffix" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> (((-100000000) <= (Znth i input 0)) /\ ((Znth i input 0) <= 100000000)))) ,
  ((( &( "suffix" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> (((-100000000) <= (Znth i input 0)) /\ ((Znth i input 0) <= 100000000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "answer" ) )) # Int64  |-> 0)
  **  ((( &( "suffix" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre input )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition solver_safety_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> (((-100000000) <= (Znth i input 0)) /\ ((Znth i input 0) <= 100000000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "answer" ) )) # Int64  |-> 0)
  **  ((( &( "suffix" ) )) # Int64  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (Int64Array.full a_pre n_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH5 : ((-1) <= i)) (PreH6 : (i < n_pre)) (PreH7 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH8 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH9 : ((-10000000000000) <= answer)) (PreH10 : ((0 <= i) -> (0 <= answer))) (PreH11 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH12 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH13 : (SuffixContributionSum input (i + 1 ) answer )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "suffix" ) )) # Int64  |-> suffix)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
  **  (Int64Array.full a_pre n_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : (i >= 0)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= (Zlength (input)))) (PreH4 : ((Zlength (input)) <= 100000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH6 : ((-1) <= i)) (PreH7 : (i < n_pre)) (PreH8 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH9 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH10 : ((-10000000000000) <= answer)) (PreH11 : ((0 <= i) -> (0 <= answer))) (PreH12 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH13 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH14 : (SuffixContributionSum input (i + 1 ) answer )) ,
  (Int64Array.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "suffix" ) )) # Int64  |-> suffix)
  **  ((( &( "answer" ) )) # Int64  |-> answer)
|--
  “ ((suffix + (Znth i input 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (suffix + (Znth i input 0) )) ”
.

Definition solver_safety_wit_7 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : (i >= 0)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= (Zlength (input)))) (PreH4 : ((Zlength (input)) <= 100000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH6 : ((-1) <= i)) (PreH7 : (i < n_pre)) (PreH8 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH9 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH10 : ((-10000000000000) <= answer)) (PreH11 : ((0 <= i) -> (0 <= answer))) (PreH12 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH13 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH14 : (SuffixContributionSum input (i + 1 ) answer )) ,
  (Int64Array.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "suffix" ) )) # Int64  |-> (suffix + (Znth i input 0) ))
  **  ((( &( "answer" ) )) # Int64  |-> answer)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : (i <> 0)) (PreH2 : (i >= 0)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH10 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH11 : ((-10000000000000) <= answer)) (PreH12 : ((0 <= i) -> (0 <= answer))) (PreH13 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH14 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH15 : (SuffixContributionSum input (i + 1 ) answer )) ,
  (Int64Array.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "suffix" ) )) # Int64  |-> (suffix + (Znth i input 0) ))
  **  ((( &( "answer" ) )) # Int64  |-> answer)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : (i = 0)) (PreH2 : (i >= 0)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH10 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH11 : ((-10000000000000) <= answer)) (PreH12 : ((0 <= i) -> (0 <= answer))) (PreH13 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH14 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH15 : (SuffixContributionSum input (i + 1 ) answer )) ,
  (Int64Array.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "suffix" ) )) # Int64  |-> (suffix + (Znth i input 0) ))
  **  ((( &( "answer" ) )) # Int64  |-> answer)
|--
  “ ((answer + (suffix + (Znth i input 0) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (answer + (suffix + (Znth i input 0) ) )) ”
.

Definition solver_safety_wit_10 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : ((suffix + (Znth i input 0) ) > 0)) (PreH2 : (i <> 0)) (PreH3 : (i >= 0)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH11 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH12 : ((-10000000000000) <= answer)) (PreH13 : ((0 <= i) -> (0 <= answer))) (PreH14 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH15 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH16 : (SuffixContributionSum input (i + 1 ) answer )) ,
  (Int64Array.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "suffix" ) )) # Int64  |-> (suffix + (Znth i input 0) ))
  **  ((( &( "answer" ) )) # Int64  |-> answer)
|--
  “ ((answer + (suffix + (Znth i input 0) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (answer + (suffix + (Znth i input 0) ) )) ”
.

Definition solver_safety_wit_11 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : (i = 0)) (PreH2 : (i >= 0)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH10 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH11 : ((-10000000000000) <= answer)) (PreH12 : ((0 <= i) -> (0 <= answer))) (PreH13 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH14 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH15 : (SuffixContributionSum input (i + 1 ) answer )) ,
  (Int64Array.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "suffix" ) )) # Int64  |-> (suffix + (Znth i input 0) ))
  **  ((( &( "answer" ) )) # Int64  |-> (answer + (suffix + (Znth i input 0) ) ))
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_12 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : ((suffix + (Znth i input 0) ) > 0)) (PreH2 : (i <> 0)) (PreH3 : (i >= 0)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH11 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH12 : ((-10000000000000) <= answer)) (PreH13 : ((0 <= i) -> (0 <= answer))) (PreH14 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH15 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH16 : (SuffixContributionSum input (i + 1 ) answer )) ,
  (Int64Array.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "suffix" ) )) # Int64  |-> (suffix + (Znth i input 0) ))
  **  ((( &( "answer" ) )) # Int64  |-> (answer + (suffix + (Znth i input 0) ) ))
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_13 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : ((suffix + (Znth i input 0) ) <= 0)) (PreH2 : (i <> 0)) (PreH3 : (i >= 0)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH11 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH12 : ((-10000000000000) <= answer)) (PreH13 : ((0 <= i) -> (0 <= answer))) (PreH14 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH15 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH16 : (SuffixContributionSum input (i + 1 ) answer )) ,
  (Int64Array.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "suffix" ) )) # Int64  |-> (suffix + (Znth i input 0) ))
  **  ((( &( "answer" ) )) # Int64  |-> answer)
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> (((-100000000) <= (Znth i input 0)) /\ ((Znth i input 0) <= 100000000)))) ,
  (Int64Array.full a_pre n_pre input )
|--
  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= (Zlength (input))) ” 
  &&  “ ((Zlength (input)) <= 100000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000))) ” 
  &&  “ ((-1) <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ (((-100000000) * ((n_pre - (n_pre - 1 ) ) - 1 ) ) <= 0) ” 
  &&  “ (0 <= (100000000 * ((n_pre - (n_pre - 1 ) ) - 1 ) )) ” 
  &&  “ ((-10000000000000) <= 0) ” 
  &&  “ ((0 <= (n_pre - 1 )) -> (0 <= 0)) ” 
  &&  “ (0 <= (((n_pre - (n_pre - 1 ) ) - 1 ) * 10000000000000 )) ” 
  &&  “ (0 = (SuffixSum (input) (((n_pre - 1 ) + 1 )))) ” 
  &&  “ (SuffixContributionSum input ((n_pre - 1 ) + 1 ) 0 ) ”
  &&  (Int64Array.full a_pre n_pre input )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> (((-100000000) <= (Znth i input 0)) /\ ((Znth i input 0) <= 100000000)))) ,
  TT && emp 
|--
  “ (SuffixContributionSum input ((n_pre - 1 ) + 1 ) 0 ) ” 
  &&  “ (0 = (SuffixSum (input) (((n_pre - 1 ) + 1 )))) ” 
  &&  “ (((-100000000) * ((n_pre - (n_pre - 1 ) ) - 1 ) ) <= 0) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> (((-100000000) <= (Znth i input 0)) /\ ((Znth i input 0) <= 100000000)))) ,
  (SuffixContributionSum input ((n_pre - 1 ) + 1 ) 0 )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> (((-100000000) <= (Znth i input 0)) /\ ((Znth i input 0) <= 100000000)))) ,
  (0 = (SuffixSum (input) (((n_pre - 1 ) + 1 ))))
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> (((-100000000) <= (Znth i input 0)) /\ ((Znth i input 0) <= 100000000)))) ,
  (((-100000000) * ((n_pre - (n_pre - 1 ) ) - 1 ) ) <= 0)
.

Definition solver_entail_wit_1_split_goal_4 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 100000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> (((-100000000) <= (Znth i input 0)) /\ ((Znth i input 0) <= 100000000)))) ,
  forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))
.

Definition solver_entail_wit_2_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : (i = 0)) (PreH2 : (i >= 0)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH10 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH11 : ((-10000000000000) <= answer)) (PreH12 : ((0 <= i) -> (0 <= answer))) (PreH13 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH14 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH15 : (SuffixContributionSum input (i + 1 ) answer )) ,
  (Int64Array.full a_pre n_pre input )
|--
  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= (Zlength (input))) ” 
  &&  “ ((Zlength (input)) <= 100000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000))) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (((-100000000) * ((n_pre - (i - 1 ) ) - 1 ) ) <= (suffix + (Znth i input 0) )) ” 
  &&  “ ((suffix + (Znth i input 0) ) <= (100000000 * ((n_pre - (i - 1 ) ) - 1 ) )) ” 
  &&  “ ((-10000000000000) <= (answer + (suffix + (Znth i input 0) ) )) ” 
  &&  “ ((0 <= (i - 1 )) -> (0 <= (answer + (suffix + (Znth i input 0) ) ))) ” 
  &&  “ ((answer + (suffix + (Znth i input 0) ) ) <= (((n_pre - (i - 1 ) ) - 1 ) * 10000000000000 )) ” 
  &&  “ ((suffix + (Znth i input 0) ) = (SuffixSum (input) (((i - 1 ) + 1 )))) ” 
  &&  “ (SuffixContributionSum input ((i - 1 ) + 1 ) (answer + (suffix + (Znth i input 0) ) ) ) ”
  &&  (Int64Array.full a_pre n_pre input )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : (i = 0)) (PreH2 : (i >= 0)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH10 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH11 : ((-10000000000000) <= answer)) (PreH12 : ((0 <= i) -> (0 <= answer))) (PreH13 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH14 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH15 : (SuffixContributionSum input (i + 1 ) answer )) ,
  TT && emp 
|--
  “ (SuffixContributionSum input ((0 - 1 ) + 1 ) (answer + (suffix + (Znth 0 input 0) ) ) ) ” 
  &&  “ ((suffix + (Znth 0 input 0) ) = (SuffixSum (input) (((0 - 1 ) + 1 )))) ” 
  &&  “ ((answer + (suffix + (Znth 0 input 0) ) ) <= (((n_pre - (0 - 1 ) ) - 1 ) * 10000000000000 )) ” 
  &&  “ (((-100000000) * ((n_pre - (0 - 1 ) ) - 1 ) ) <= (suffix + (Znth 0 input 0) )) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : (i = 0)) (PreH2 : (i >= 0)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH10 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH11 : ((-10000000000000) <= answer)) (PreH12 : ((0 <= i) -> (0 <= answer))) (PreH13 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH14 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH15 : (SuffixContributionSum input (i + 1 ) answer )) ,
  (SuffixContributionSum input ((0 - 1 ) + 1 ) (answer + (suffix + (Znth 0 input 0) ) ) )
.

Definition solver_entail_wit_2_1_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : (i = 0)) (PreH2 : (i >= 0)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH10 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH11 : ((-10000000000000) <= answer)) (PreH12 : ((0 <= i) -> (0 <= answer))) (PreH13 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH14 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH15 : (SuffixContributionSum input (i + 1 ) answer )) ,
  ((suffix + (Znth 0 input 0) ) = (SuffixSum (input) (((0 - 1 ) + 1 ))))
.

Definition solver_entail_wit_2_1_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : (i = 0)) (PreH2 : (i >= 0)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH10 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH11 : ((-10000000000000) <= answer)) (PreH12 : ((0 <= i) -> (0 <= answer))) (PreH13 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH14 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH15 : (SuffixContributionSum input (i + 1 ) answer )) ,
  ((answer + (suffix + (Znth 0 input 0) ) ) <= (((n_pre - (0 - 1 ) ) - 1 ) * 10000000000000 ))
.

Definition solver_entail_wit_2_1_split_goal_4 := 
forall (n_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : (i = 0)) (PreH2 : (i >= 0)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= (Zlength (input)))) (PreH5 : ((Zlength (input)) <= 100000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH7 : ((-1) <= i)) (PreH8 : (i < n_pre)) (PreH9 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH10 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH11 : ((-10000000000000) <= answer)) (PreH12 : ((0 <= i) -> (0 <= answer))) (PreH13 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH14 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH15 : (SuffixContributionSum input (i + 1 ) answer )) ,
  (((-100000000) * ((n_pre - (0 - 1 ) ) - 1 ) ) <= (suffix + (Znth 0 input 0) ))
.

Definition solver_entail_wit_2_2 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : ((suffix + (Znth i input 0) ) > 0)) (PreH2 : (i <> 0)) (PreH3 : (i >= 0)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH11 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH12 : ((-10000000000000) <= answer)) (PreH13 : ((0 <= i) -> (0 <= answer))) (PreH14 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH15 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH16 : (SuffixContributionSum input (i + 1 ) answer )) ,
  (Int64Array.full a_pre n_pre input )
|--
  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= (Zlength (input))) ” 
  &&  “ ((Zlength (input)) <= 100000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000))) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (((-100000000) * ((n_pre - (i - 1 ) ) - 1 ) ) <= (suffix + (Znth i input 0) )) ” 
  &&  “ ((suffix + (Znth i input 0) ) <= (100000000 * ((n_pre - (i - 1 ) ) - 1 ) )) ” 
  &&  “ ((-10000000000000) <= (answer + (suffix + (Znth i input 0) ) )) ” 
  &&  “ ((0 <= (i - 1 )) -> (0 <= (answer + (suffix + (Znth i input 0) ) ))) ” 
  &&  “ ((answer + (suffix + (Znth i input 0) ) ) <= (((n_pre - (i - 1 ) ) - 1 ) * 10000000000000 )) ” 
  &&  “ ((suffix + (Znth i input 0) ) = (SuffixSum (input) (((i - 1 ) + 1 )))) ” 
  &&  “ (SuffixContributionSum input ((i - 1 ) + 1 ) (answer + (suffix + (Znth i input 0) ) ) ) ”
  &&  (Int64Array.full a_pre n_pre input )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : ((suffix + (Znth i input 0) ) > 0)) (PreH2 : (i <> 0)) (PreH3 : (i >= 0)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH11 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH12 : ((-10000000000000) <= answer)) (PreH13 : ((0 <= i) -> (0 <= answer))) (PreH14 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH15 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH16 : (SuffixContributionSum input (i + 1 ) answer )) ,
  TT && emp 
|--
  “ (SuffixContributionSum input ((i - 1 ) + 1 ) (answer + (suffix + (Znth i input 0) ) ) ) ” 
  &&  “ ((suffix + (Znth i input 0) ) = (SuffixSum (input) (((i - 1 ) + 1 )))) ” 
  &&  “ ((answer + (suffix + (Znth i input 0) ) ) <= (((n_pre - (i - 1 ) ) - 1 ) * 10000000000000 )) ” 
  &&  “ (((-100000000) * ((n_pre - (i - 1 ) ) - 1 ) ) <= (suffix + (Znth i input 0) )) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : ((suffix + (Znth i input 0) ) > 0)) (PreH2 : (i <> 0)) (PreH3 : (i >= 0)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH11 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH12 : ((-10000000000000) <= answer)) (PreH13 : ((0 <= i) -> (0 <= answer))) (PreH14 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH15 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH16 : (SuffixContributionSum input (i + 1 ) answer )) ,
  (SuffixContributionSum input ((i - 1 ) + 1 ) (answer + (suffix + (Znth i input 0) ) ) )
.

Definition solver_entail_wit_2_2_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : ((suffix + (Znth i input 0) ) > 0)) (PreH2 : (i <> 0)) (PreH3 : (i >= 0)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH11 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH12 : ((-10000000000000) <= answer)) (PreH13 : ((0 <= i) -> (0 <= answer))) (PreH14 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH15 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH16 : (SuffixContributionSum input (i + 1 ) answer )) ,
  ((suffix + (Znth i input 0) ) = (SuffixSum (input) (((i - 1 ) + 1 ))))
.

Definition solver_entail_wit_2_2_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : ((suffix + (Znth i input 0) ) > 0)) (PreH2 : (i <> 0)) (PreH3 : (i >= 0)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH11 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH12 : ((-10000000000000) <= answer)) (PreH13 : ((0 <= i) -> (0 <= answer))) (PreH14 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH15 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH16 : (SuffixContributionSum input (i + 1 ) answer )) ,
  ((answer + (suffix + (Znth i input 0) ) ) <= (((n_pre - (i - 1 ) ) - 1 ) * 10000000000000 ))
.

Definition solver_entail_wit_2_2_split_goal_4 := 
forall (n_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : ((suffix + (Znth i input 0) ) > 0)) (PreH2 : (i <> 0)) (PreH3 : (i >= 0)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH11 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH12 : ((-10000000000000) <= answer)) (PreH13 : ((0 <= i) -> (0 <= answer))) (PreH14 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH15 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH16 : (SuffixContributionSum input (i + 1 ) answer )) ,
  (((-100000000) * ((n_pre - (i - 1 ) ) - 1 ) ) <= (suffix + (Znth i input 0) ))
.

Definition solver_entail_wit_2_3 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : ((suffix + (Znth i input 0) ) <= 0)) (PreH2 : (i <> 0)) (PreH3 : (i >= 0)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH11 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH12 : ((-10000000000000) <= answer)) (PreH13 : ((0 <= i) -> (0 <= answer))) (PreH14 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH15 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH16 : (SuffixContributionSum input (i + 1 ) answer )) ,
  (Int64Array.full a_pre n_pre input )
|--
  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= (Zlength (input))) ” 
  &&  “ ((Zlength (input)) <= 100000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000))) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (((-100000000) * ((n_pre - (i - 1 ) ) - 1 ) ) <= (suffix + (Znth i input 0) )) ” 
  &&  “ ((suffix + (Znth i input 0) ) <= (100000000 * ((n_pre - (i - 1 ) ) - 1 ) )) ” 
  &&  “ ((-10000000000000) <= answer) ” 
  &&  “ ((0 <= (i - 1 )) -> (0 <= answer)) ” 
  &&  “ (answer <= (((n_pre - (i - 1 ) ) - 1 ) * 10000000000000 )) ” 
  &&  “ ((suffix + (Znth i input 0) ) = (SuffixSum (input) (((i - 1 ) + 1 )))) ” 
  &&  “ (SuffixContributionSum input ((i - 1 ) + 1 ) answer ) ”
  &&  (Int64Array.full a_pre n_pre input )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : ((suffix + (Znth i input 0) ) <= 0)) (PreH2 : (i <> 0)) (PreH3 : (i >= 0)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH11 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH12 : ((-10000000000000) <= answer)) (PreH13 : ((0 <= i) -> (0 <= answer))) (PreH14 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH15 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH16 : (SuffixContributionSum input (i + 1 ) answer )) ,
  TT && emp 
|--
  “ (SuffixContributionSum input ((i - 1 ) + 1 ) answer ) ” 
  &&  “ ((suffix + (Znth i input 0) ) = (SuffixSum (input) (((i - 1 ) + 1 )))) ” 
  &&  “ (((-100000000) * ((n_pre - (i - 1 ) ) - 1 ) ) <= (suffix + (Znth i input 0) )) ”
  &&  emp
).

Definition solver_entail_wit_2_3_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : ((suffix + (Znth i input 0) ) <= 0)) (PreH2 : (i <> 0)) (PreH3 : (i >= 0)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH11 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH12 : ((-10000000000000) <= answer)) (PreH13 : ((0 <= i) -> (0 <= answer))) (PreH14 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH15 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH16 : (SuffixContributionSum input (i + 1 ) answer )) ,
  (SuffixContributionSum input ((i - 1 ) + 1 ) answer )
.

Definition solver_entail_wit_2_3_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : ((suffix + (Znth i input 0) ) <= 0)) (PreH2 : (i <> 0)) (PreH3 : (i >= 0)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH11 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH12 : ((-10000000000000) <= answer)) (PreH13 : ((0 <= i) -> (0 <= answer))) (PreH14 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH15 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH16 : (SuffixContributionSum input (i + 1 ) answer )) ,
  ((suffix + (Znth i input 0) ) = (SuffixSum (input) (((i - 1 ) + 1 ))))
.

Definition solver_entail_wit_2_3_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : ((suffix + (Znth i input 0) ) <= 0)) (PreH2 : (i <> 0)) (PreH3 : (i >= 0)) (PreH4 : (n_pre = (Zlength (input)))) (PreH5 : (1 <= (Zlength (input)))) (PreH6 : ((Zlength (input)) <= 100000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH8 : ((-1) <= i)) (PreH9 : (i < n_pre)) (PreH10 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH11 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH12 : ((-10000000000000) <= answer)) (PreH13 : ((0 <= i) -> (0 <= answer))) (PreH14 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH15 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH16 : (SuffixContributionSum input (i + 1 ) answer )) ,
  (((-100000000) * ((n_pre - (i - 1 ) ) - 1 ) ) <= (suffix + (Znth i input 0) ))
.

Definition solver_return_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : (i < 0)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= (Zlength (input)))) (PreH4 : ((Zlength (input)) <= 100000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH6 : ((-1) <= i)) (PreH7 : (i < n_pre)) (PreH8 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH9 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH10 : ((-10000000000000) <= answer)) (PreH11 : ((0 <= i) -> (0 <= answer))) (PreH12 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH13 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH14 : (SuffixContributionSum input (i + 1 ) answer )) ,
  (Int64Array.full a_pre n_pre input )
|--
  “ (Spec input answer ) ”
  &&  (Int64Array.full a_pre n_pre input )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : (i < 0)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= (Zlength (input)))) (PreH4 : ((Zlength (input)) <= 100000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH6 : ((-1) <= i)) (PreH7 : (i < n_pre)) (PreH8 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH9 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH10 : ((-10000000000000) <= answer)) (PreH11 : ((0 <= i) -> (0 <= answer))) (PreH12 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH13 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH14 : (SuffixContributionSum input (i + 1 ) answer )) ,
  TT && emp 
|--
  “ (Spec input answer ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : (i < 0)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= (Zlength (input)))) (PreH4 : ((Zlength (input)) <= 100000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH6 : ((-1) <= i)) (PreH7 : (i < n_pre)) (PreH8 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH9 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH10 : ((-10000000000000) <= answer)) (PreH11 : ((0 <= i) -> (0 <= answer))) (PreH12 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH13 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH14 : (SuffixContributionSum input (i + 1 ) answer )) ,
  (Spec input answer )
.

Definition solver_partial_solve_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (answer: Z) (suffix: Z) (i: Z) (PreH1 : (i >= 0)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= (Zlength (input)))) (PreH4 : ((Zlength (input)) <= 100000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000)))) (PreH6 : ((-1) <= i)) (PreH7 : (i < n_pre)) (PreH8 : (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix)) (PreH9 : (suffix <= (100000000 * ((n_pre - i ) - 1 ) ))) (PreH10 : ((-10000000000000) <= answer)) (PreH11 : ((0 <= i) -> (0 <= answer))) (PreH12 : (answer <= (((n_pre - i ) - 1 ) * 10000000000000 ))) (PreH13 : (suffix = (SuffixSum (input) ((i + 1 ))))) (PreH14 : (SuffixContributionSum input (i + 1 ) answer )) ,
  (Int64Array.full a_pre n_pre input )
|--
  “ (i >= 0) ” 
  &&  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= (Zlength (input))) ” 
  &&  “ ((Zlength (input)) <= 100000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (input)))) -> (((-100000000) <= (Znth j input 0)) /\ ((Znth j input 0) <= 100000000))) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (((-100000000) * ((n_pre - i ) - 1 ) ) <= suffix) ” 
  &&  “ (suffix <= (100000000 * ((n_pre - i ) - 1 ) )) ” 
  &&  “ ((-10000000000000) <= answer) ” 
  &&  “ ((0 <= i) -> (0 <= answer)) ” 
  &&  “ (answer <= (((n_pre - i ) - 1 ) * 10000000000000 )) ” 
  &&  “ (suffix = (SuffixSum (input) ((i + 1 )))) ” 
  &&  “ (SuffixContributionSum input (i + 1 ) answer ) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i input 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre input )
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

End VC_Correct.
