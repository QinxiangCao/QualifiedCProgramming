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
Require Import SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.
Local Open Scope sac.

(*----- Function rob -----*)

Definition rob_safety_wit_1 := 
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall (Z.le (0)) l )) (PreH5 : (Forall (Z.ge (10000)) l )) ,
  ((( &( "prev2" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full nums_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rob_safety_wit_2 := 
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall (Z.le (0)) l )) (PreH5 : (Forall (Z.ge (10000)) l )) ,
  ((( &( "prev1" ) )) # Int  |->_)
  **  ((( &( "prev2" ) )) # Int  |-> 0)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full nums_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rob_safety_wit_3 := 
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall (Z.le (0)) l )) (PreH5 : (Forall (Z.ge (10000)) l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "prev1" ) )) # Int  |-> 0)
  **  ((( &( "prev2" ) )) # Int  |-> 0)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full nums_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rob_safety_wit_4 := 
(
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall (Z.le (0)) l )) (PreH5 : (Forall (Z.ge (10000)) l )) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (HouseRobberDPState l i prev2 prev1 )) ,
  (IntArray.full nums_pre n_pre l )
  **  ((( &( "take" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev1" ) )) # Int  |-> prev1)
  **  ((( &( "prev2" ) )) # Int  |-> prev2)
|--
  “ ((prev2 + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (prev2 + (Znth i l 0) )) ”
) \/
(
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall (Z.le (0)) l )) (PreH5 : (Forall (Z.ge (10000)) l )) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (HouseRobberDPState l i prev2 prev1 )) ,
  (IntArray.full nums_pre n_pre l )
  **  ((( &( "take" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev1" ) )) # Int  |-> prev1)
  **  ((( &( "prev2" ) )) # Int  |-> prev2)
|--
  “ ((prev2 + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (prev2 + (Znth i l 0) )) ”
).

Definition rob_safety_wit_4_split_goal_1 := 
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall (Z.le (0)) l )) (PreH5 : (Forall (Z.ge (10000)) l )) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (HouseRobberDPState l i prev2 prev1 )) ,
  (IntArray.full nums_pre n_pre l )
  **  ((( &( "take" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev1" ) )) # Int  |-> prev1)
  **  ((( &( "prev2" ) )) # Int  |-> prev2)
|--
  “ ((prev2 + (Znth i l 0) ) <= INT_MAX) ”
.

Definition rob_safety_wit_4_split_goal_2 := 
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall (Z.le (0)) l )) (PreH5 : (Forall (Z.ge (10000)) l )) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (HouseRobberDPState l i prev2 prev1 )) ,
  (IntArray.full nums_pre n_pre l )
  **  ((( &( "take" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev1" ) )) # Int  |-> prev1)
  **  ((( &( "prev2" ) )) # Int  |-> prev2)
|--
  “ ((INT_MIN) <= (prev2 + (Znth i l 0) )) ”
.

Definition rob_safety_wit_5 := 
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i: Z) (PreH1 : ((prev2 + (Znth i l 0) ) > prev1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le (0)) l )) (PreH6 : (Forall (Z.ge (10000)) l )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (HouseRobberDPState l i prev2 prev1 )) ,
  (IntArray.full nums_pre n_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev1" ) )) # Int  |-> (prev2 + (Znth i l 0) ))
  **  ((( &( "prev2" ) )) # Int  |-> prev1)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition rob_safety_wit_6 := 
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i: Z) (PreH1 : ((prev2 + (Znth i l 0) ) <= prev1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le (0)) l )) (PreH6 : (Forall (Z.ge (10000)) l )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (HouseRobberDPState l i prev2 prev1 )) ,
  (IntArray.full nums_pre n_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev1" ) )) # Int  |-> prev1)
  **  ((( &( "prev2" ) )) # Int  |-> prev1)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition rob_entail_wit_1 := 
(
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall (Z.le (0)) l )) (PreH5 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full nums_pre n_pre l )
|--
  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (HouseRobberDPState l 0 0 0 ) ”
  &&  (IntArray.full nums_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall (Z.le (0)) l )) (PreH5 : (Forall (Z.ge (10000)) l )) ,
  TT && emp 
|--
  “ (HouseRobberDPState l 0 0 0 ) ”
  &&  emp
).

Definition rob_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall (Z.le (0)) l )) (PreH5 : (Forall (Z.ge (10000)) l )) ,
  (HouseRobberDPState l 0 0 0 )
.

Definition rob_entail_wit_2_1 := 
(
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i: Z) (PreH1 : ((prev2 + (Znth i l 0) ) > prev1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le (0)) l )) (PreH6 : (Forall (Z.ge (10000)) l )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (HouseRobberDPState l i prev2 prev1 )) ,
  (IntArray.full nums_pre n_pre l )
|--
  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (HouseRobberDPState l (i + 1 ) prev1 (prev2 + (Znth i l 0) ) ) ”
  &&  (IntArray.full nums_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i: Z) (PreH1 : ((prev2 + (Znth i l 0) ) > prev1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le (0)) l )) (PreH6 : (Forall (Z.ge (10000)) l )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (HouseRobberDPState l i prev2 prev1 )) ,
  TT && emp 
|--
  “ (HouseRobberDPState l (i + 1 ) prev1 (prev2 + (Znth i l 0) ) ) ”
  &&  emp
).

Definition rob_entail_wit_2_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i: Z) (PreH1 : ((prev2 + (Znth i l 0) ) > prev1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le (0)) l )) (PreH6 : (Forall (Z.ge (10000)) l )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (HouseRobberDPState l i prev2 prev1 )) ,
  (HouseRobberDPState l (i + 1 ) prev1 (prev2 + (Znth i l 0) ) )
.

Definition rob_entail_wit_2_2 := 
(
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i: Z) (PreH1 : ((prev2 + (Znth i l 0) ) <= prev1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le (0)) l )) (PreH6 : (Forall (Z.ge (10000)) l )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (HouseRobberDPState l i prev2 prev1 )) ,
  (IntArray.full nums_pre n_pre l )
|--
  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (HouseRobberDPState l (i + 1 ) prev1 prev1 ) ”
  &&  (IntArray.full nums_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i: Z) (PreH1 : ((prev2 + (Znth i l 0) ) <= prev1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le (0)) l )) (PreH6 : (Forall (Z.ge (10000)) l )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (HouseRobberDPState l i prev2 prev1 )) ,
  TT && emp 
|--
  “ (HouseRobberDPState l (i + 1 ) prev1 prev1 ) ”
  &&  emp
).

Definition rob_entail_wit_2_2_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i: Z) (PreH1 : ((prev2 + (Znth i l 0) ) <= prev1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le (0)) l )) (PreH6 : (Forall (Z.ge (10000)) l )) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (HouseRobberDPState l i prev2 prev1 )) ,
  (HouseRobberDPState l (i + 1 ) prev1 prev1 )
.

Definition rob_return_wit_1 := 
(
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall (Z.le (0)) l )) (PreH5 : (Forall (Z.ge (10000)) l )) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (HouseRobberDPState l i prev2 prev1 )) ,
  (IntArray.full nums_pre n_pre l )
|--
  “ (HouseRobberAnswer l prev1 ) ”
  &&  (IntArray.full nums_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall (Z.le (0)) l )) (PreH5 : (Forall (Z.ge (10000)) l )) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (HouseRobberDPState l i prev2 prev1 )) ,
  TT && emp 
|--
  “ (HouseRobberAnswer l prev1 ) ”
  &&  emp
).

Definition rob_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall (Z.le (0)) l )) (PreH5 : (Forall (Z.ge (10000)) l )) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (HouseRobberDPState l i prev2 prev1 )) ,
  (HouseRobberAnswer l prev1 )
.

Definition rob_partial_solve_wit_1 := 
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (prev2: Z) (prev1: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall (Z.le (0)) l )) (PreH5 : (Forall (Z.ge (10000)) l )) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (HouseRobberDPState l i prev2 prev1 )) ,
  (IntArray.full nums_pre n_pre l )
|--
  “ (i < n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (HouseRobberDPState l i prev2 prev1 ) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i nums_pre i 0 n_pre l )
.

Module Type VC_Correct.


Axiom proof_of_rob_safety_wit_1 : rob_safety_wit_1.
Axiom proof_of_rob_safety_wit_2 : rob_safety_wit_2.
Axiom proof_of_rob_safety_wit_3 : rob_safety_wit_3.
Axiom proof_of_rob_safety_wit_4 : rob_safety_wit_4.
Axiom proof_of_rob_safety_wit_5 : rob_safety_wit_5.
Axiom proof_of_rob_safety_wit_6 : rob_safety_wit_6.
Axiom proof_of_rob_entail_wit_1 : rob_entail_wit_1.
Axiom proof_of_rob_entail_wit_2_1 : rob_entail_wit_2_1.
Axiom proof_of_rob_entail_wit_2_2 : rob_entail_wit_2_2.
Axiom proof_of_rob_return_wit_1 : rob_return_wit_1.
Axiom proof_of_rob_partial_solve_wit_1 : rob_partial_solve_wit_1.

End VC_Correct.
