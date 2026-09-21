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
Require Import SimpleC.EE.LLM_bench.Algorithms.climbing_stairs.climbing_stairs_lib.
Local Open Scope sac.

(*----- Function climbStairs -----*)

Definition climbStairs_safety_wit_1 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 45)) ,
  ((( &( "prev" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition climbStairs_safety_wit_2 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 45)) ,
  ((( &( "curr" ) )) # Int  |->_)
  **  ((( &( "prev" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition climbStairs_safety_wit_3 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 45)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "curr" ) )) # Int  |-> 1)
  **  ((( &( "prev" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition climbStairs_safety_wit_4 := 
(
forall (n_pre: Z) (curr: Z) (prev: Z) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 45)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (0 <= prev)) (PreH7 : (0 <= curr)) (PreH8 : (ClimbingStairsCount (i - 2 ) prev )) (PreH9 : (ClimbingStairsCount (i - 1 ) curr )) ,
  ((( &( "next" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev" ) )) # Int  |-> prev)
  **  ((( &( "curr" ) )) # Int  |-> curr)
|--
  “ ((prev + curr ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (prev + curr )) ”
) \/
(
forall (n_pre: Z) (curr: Z) (prev: Z) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 45)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (0 <= prev)) (PreH7 : (0 <= curr)) (PreH8 : (ClimbingStairsCount (i - 2 ) prev )) (PreH9 : (ClimbingStairsCount (i - 1 ) curr )) ,
  ((( &( "next" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev" ) )) # Int  |-> prev)
  **  ((( &( "curr" ) )) # Int  |-> curr)
|--
  “ ((prev + curr ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (prev + curr )) ”
).

Definition climbStairs_safety_wit_4_split_goal_1 := 
forall (n_pre: Z) (curr: Z) (prev: Z) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 45)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (0 <= prev)) (PreH7 : (0 <= curr)) (PreH8 : (ClimbingStairsCount (i - 2 ) prev )) (PreH9 : (ClimbingStairsCount (i - 1 ) curr )) ,
  ((( &( "next" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev" ) )) # Int  |-> prev)
  **  ((( &( "curr" ) )) # Int  |-> curr)
|--
  “ ((prev + curr ) <= INT_MAX) ”
.

Definition climbStairs_safety_wit_4_split_goal_2 := 
forall (n_pre: Z) (curr: Z) (prev: Z) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 45)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (0 <= prev)) (PreH7 : (0 <= curr)) (PreH8 : (ClimbingStairsCount (i - 2 ) prev )) (PreH9 : (ClimbingStairsCount (i - 1 ) curr )) ,
  ((( &( "next" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev" ) )) # Int  |-> prev)
  **  ((( &( "curr" ) )) # Int  |-> curr)
|--
  “ ((INT_MIN) <= (prev + curr )) ”
.

Definition climbStairs_safety_wit_5 := 
forall (n_pre: Z) (curr: Z) (prev: Z) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 45)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (0 <= prev)) (PreH7 : (0 <= curr)) (PreH8 : (ClimbingStairsCount (i - 2 ) prev )) (PreH9 : (ClimbingStairsCount (i - 1 ) curr )) ,
  ((( &( "next" ) )) # Int  |-> (prev + curr ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev" ) )) # Int  |-> curr)
  **  ((( &( "curr" ) )) # Int  |-> (prev + curr ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition climbStairs_safety_wit_6 := 
forall (n_pre: Z) (curr: Z) (prev: Z) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 45)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (0 <= prev)) (PreH7 : (0 <= curr)) (PreH8 : (ClimbingStairsCount (i - 2 ) prev )) (PreH9 : (ClimbingStairsCount (i - 1 ) curr )) ,
  ((( &( "next" ) )) # Int  |-> (prev + curr ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev" ) )) # Int  |-> curr)
  **  ((( &( "curr" ) )) # Int  |-> (prev + curr ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition climbStairs_entail_wit_1 := 
(
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 45)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 45) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= (n_pre + 1 )) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (ClimbingStairsCount (2 - 2 ) 1 ) ” 
  &&  “ (ClimbingStairsCount (2 - 1 ) 1 ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 45)) ,
  TT && emp 
|--
  “ (ClimbingStairsCount (2 - 1 ) 1 ) ” 
  &&  “ (ClimbingStairsCount (2 - 2 ) 1 ) ”
  &&  emp
).

Definition climbStairs_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 45)) ,
  (ClimbingStairsCount (2 - 1 ) 1 )
.

Definition climbStairs_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 45)) ,
  (ClimbingStairsCount (2 - 2 ) 1 )
.

Definition climbStairs_entail_wit_2 := 
(
forall (n_pre: Z) (curr: Z) (prev: Z) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 45)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (0 <= prev)) (PreH7 : (0 <= curr)) (PreH8 : (ClimbingStairsCount (i - 2 ) prev )) (PreH9 : (ClimbingStairsCount (i - 1 ) curr )) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 45) ” 
  &&  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= curr) ” 
  &&  “ (0 <= (prev + curr )) ” 
  &&  “ (ClimbingStairsCount ((i + 1 ) - 2 ) curr ) ” 
  &&  “ (ClimbingStairsCount ((i + 1 ) - 1 ) (prev + curr ) ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (curr: Z) (prev: Z) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 45)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (0 <= prev)) (PreH7 : (0 <= curr)) (PreH8 : (ClimbingStairsCount (i - 2 ) prev )) (PreH9 : (ClimbingStairsCount (i - 1 ) curr )) ,
  TT && emp 
|--
  “ (ClimbingStairsCount ((i + 1 ) - 1 ) (prev + curr ) ) ” 
  &&  “ (ClimbingStairsCount ((i + 1 ) - 2 ) curr ) ”
  &&  emp
).

Definition climbStairs_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (curr: Z) (prev: Z) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 45)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (0 <= prev)) (PreH7 : (0 <= curr)) (PreH8 : (ClimbingStairsCount (i - 2 ) prev )) (PreH9 : (ClimbingStairsCount (i - 1 ) curr )) ,
  (ClimbingStairsCount ((i + 1 ) - 1 ) (prev + curr ) )
.

Definition climbStairs_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (curr: Z) (prev: Z) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 45)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (0 <= prev)) (PreH7 : (0 <= curr)) (PreH8 : (ClimbingStairsCount (i - 2 ) prev )) (PreH9 : (ClimbingStairsCount (i - 1 ) curr )) ,
  (ClimbingStairsCount ((i + 1 ) - 2 ) curr )
.

Definition climbStairs_return_wit_1 := 
(
forall (n_pre: Z) (curr: Z) (prev: Z) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 45)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (0 <= prev)) (PreH7 : (0 <= curr)) (PreH8 : (ClimbingStairsCount (i - 2 ) prev )) (PreH9 : (ClimbingStairsCount (i - 1 ) curr )) ,
  TT && emp 
|--
  “ (ClimbingStairsCount n_pre curr ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (curr: Z) (prev: Z) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 45)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (0 <= prev)) (PreH7 : (0 <= curr)) (PreH8 : (ClimbingStairsCount (i - 2 ) prev )) (PreH9 : (ClimbingStairsCount (i - 1 ) curr )) ,
  TT && emp 
|--
  “ (ClimbingStairsCount n_pre curr ) ”
  &&  emp
).

Definition climbStairs_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (curr: Z) (prev: Z) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 45)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (0 <= prev)) (PreH7 : (0 <= curr)) (PreH8 : (ClimbingStairsCount (i - 2 ) prev )) (PreH9 : (ClimbingStairsCount (i - 1 ) curr )) ,
  (ClimbingStairsCount n_pre curr )
.

Module Type VC_Correct.


Axiom proof_of_climbStairs_safety_wit_1 : climbStairs_safety_wit_1.
Axiom proof_of_climbStairs_safety_wit_2 : climbStairs_safety_wit_2.
Axiom proof_of_climbStairs_safety_wit_3 : climbStairs_safety_wit_3.
Axiom proof_of_climbStairs_safety_wit_4 : climbStairs_safety_wit_4.
Axiom proof_of_climbStairs_safety_wit_5 : climbStairs_safety_wit_5.
Axiom proof_of_climbStairs_safety_wit_6 : climbStairs_safety_wit_6.
Axiom proof_of_climbStairs_entail_wit_1 : climbStairs_entail_wit_1.
Axiom proof_of_climbStairs_entail_wit_2 : climbStairs_entail_wit_2.
Axiom proof_of_climbStairs_return_wit_1 : climbStairs_return_wit_1.

End VC_Correct.
