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
Require Import SimpleC.EE.QCP_demos_LLM.majorityElement_lib.
Local Open Scope sac.

(*----- Function majorityElement -----*)

Definition majorityElement_safety_wit_1 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (x: Z) (PreH1 : (IsMajorityElement x l )) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) ,
  ((( &( "vote" ) )) # Int  |->_)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre numsSize_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition majorityElement_safety_wit_2 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (x: Z) (PreH1 : (IsMajorityElement x l )) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "vote" ) )) # Int  |-> 0)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre numsSize_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition majorityElement_safety_wit_3 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (x: Z) (PreH1 : (IsMajorityElement x l )) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "candidate" ) )) # Int  |-> 0)
  **  ((( &( "vote" ) )) # Int  |-> 0)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre numsSize_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition majorityElement_safety_wit_4 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (candidate: Z) (x: Z) (vote: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (i < numsSize_pre)) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (i = (Zlength (l1)))) (PreH4 : (0 <= i)) (PreH5 : (i <= numsSize_pre)) (PreH6 : (1 <= numsSize_pre)) (PreH7 : (numsSize_pre <= 50000)) (PreH8 : (0 <= vote)) (PreH9 : (vote <= i)) (PreH10 : (IsMajorityElement x l )) (PreH11 : (MajorityOnReduced x candidate vote l2 )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vote" ) )) # Int  |-> vote)
  **  ((( &( "candidate" ) )) # Int  |-> candidate)
  **  (IntArray.full nums_pre numsSize_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition majorityElement_safety_wit_5 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (candidate: Z) (x: Z) (vote: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (vote = 0)) (PreH2 : (i < numsSize_pre)) (PreH3 : (l = (app (l1) (l2)))) (PreH4 : (i = (Zlength (l1)))) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= numsSize_pre)) (PreH8 : (numsSize_pre <= 50000)) (PreH9 : (0 <= vote)) (PreH10 : (vote <= i)) (PreH11 : (IsMajorityElement x l )) (PreH12 : (MajorityOnReduced x candidate vote l2 )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vote" ) )) # Int  |-> vote)
  **  ((( &( "candidate" ) )) # Int  |-> (Znth i l 0))
|--
  “ ((vote + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (vote + 1 )) ”
.

Definition majorityElement_safety_wit_6 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (candidate: Z) (x: Z) (vote: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (vote = 0)) (PreH2 : (i < numsSize_pre)) (PreH3 : (l = (app (l1) (l2)))) (PreH4 : (i = (Zlength (l1)))) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= numsSize_pre)) (PreH8 : (numsSize_pre <= 50000)) (PreH9 : (0 <= vote)) (PreH10 : (vote <= i)) (PreH11 : (IsMajorityElement x l )) (PreH12 : (MajorityOnReduced x candidate vote l2 )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vote" ) )) # Int  |-> vote)
  **  ((( &( "candidate" ) )) # Int  |-> (Znth i l 0))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition majorityElement_safety_wit_7 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (candidate: Z) (x: Z) (vote: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : ((Znth i l 0) <> candidate)) (PreH2 : (vote <> 0)) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (app (l1) (l2)))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : (0 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : (0 <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x l )) (PreH13 : (MajorityOnReduced x candidate vote l2 )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vote" ) )) # Int  |-> vote)
  **  ((( &( "candidate" ) )) # Int  |-> candidate)
|--
  “ ((vote + (-1) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (vote + (-1) )) ”
.

Definition majorityElement_safety_wit_8 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (candidate: Z) (x: Z) (vote: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : ((Znth i l 0) = candidate)) (PreH2 : (vote <> 0)) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (app (l1) (l2)))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : (0 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : (0 <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x l )) (PreH13 : (MajorityOnReduced x candidate vote l2 )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vote" ) )) # Int  |-> vote)
  **  ((( &( "candidate" ) )) # Int  |-> candidate)
|--
  “ ((vote + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (vote + 1 )) ”
.

Definition majorityElement_safety_wit_9 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (candidate: Z) (x: Z) (vote: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : ((Znth i l 0) = candidate)) (PreH2 : (vote <> 0)) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (app (l1) (l2)))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : (0 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : (0 <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x l )) (PreH13 : (MajorityOnReduced x candidate vote l2 )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vote" ) )) # Int  |-> vote)
  **  ((( &( "candidate" ) )) # Int  |-> candidate)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition majorityElement_safety_wit_10 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (candidate: Z) (x: Z) (vote: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : ((Znth i l 0) <> candidate)) (PreH2 : (vote <> 0)) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (app (l1) (l2)))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : (0 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : (0 <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x l )) (PreH13 : (MajorityOnReduced x candidate vote l2 )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vote" ) )) # Int  |-> vote)
  **  ((( &( "candidate" ) )) # Int  |-> candidate)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition majorityElement_safety_wit_11 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (candidate: Z) (x: Z) (vote: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : ((Znth i l 0) <> candidate)) (PreH2 : (vote <> 0)) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (app (l1) (l2)))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : (0 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : (0 <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x l )) (PreH13 : (MajorityOnReduced x candidate vote l2 )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vote" ) )) # Int  |-> vote)
  **  ((( &( "candidate" ) )) # Int  |-> candidate)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition majorityElement_safety_wit_12 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (candidate: Z) (x: Z) (vote: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (vote = 0)) (PreH2 : (i < numsSize_pre)) (PreH3 : (l = (app (l1) (l2)))) (PreH4 : (i = (Zlength (l1)))) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= numsSize_pre)) (PreH8 : (numsSize_pre <= 50000)) (PreH9 : (0 <= vote)) (PreH10 : (vote <= i)) (PreH11 : (IsMajorityElement x l )) (PreH12 : (MajorityOnReduced x candidate vote l2 )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vote" ) )) # Int  |-> (vote + 1 ))
  **  ((( &( "candidate" ) )) # Int  |-> (Znth i l 0))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition majorityElement_safety_wit_13 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (candidate: Z) (x: Z) (vote: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : ((Znth i l 0) = candidate)) (PreH2 : (vote <> 0)) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (app (l1) (l2)))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : (0 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : (0 <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x l )) (PreH13 : (MajorityOnReduced x candidate vote l2 )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vote" ) )) # Int  |-> (vote + 1 ))
  **  ((( &( "candidate" ) )) # Int  |-> candidate)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition majorityElement_safety_wit_14 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (candidate: Z) (x: Z) (vote: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : ((Znth i l 0) <> candidate)) (PreH2 : (vote <> 0)) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (app (l1) (l2)))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : (0 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : (0 <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x l )) (PreH13 : (MajorityOnReduced x candidate vote l2 )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vote" ) )) # Int  |-> (vote + (-1) ))
  **  ((( &( "candidate" ) )) # Int  |-> candidate)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition majorityElement_entail_wit_1 := 
(
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (x_2: Z) (PreH1 : (IsMajorityElement x_2 l )) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) ,
  (IntArray.full nums_pre numsSize_pre l )
|--
  EX (x: Z)  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ (0 = (Zlength (l1))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (IsMajorityElement x l ) ” 
  &&  “ (MajorityOnReduced x 0 0 l2 ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (x_2: Z) (PreH1 : (IsMajorityElement x_2 l )) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) ,
  TT && emp 
|--
  EX (x: Z)  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ (0 = (Zlength (l1))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (IsMajorityElement x l ) ” 
  &&  “ (MajorityOnReduced x 0 0 l2 ) ”
  &&  emp
).

Definition majorityElement_entail_wit_2_1 := 
(
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (candidate: Z) (x_2: Z) (vote: Z) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (PreH1 : (vote = 0)) (PreH2 : (i < numsSize_pre)) (PreH3 : (l = (app (l1_2) (l2_2)))) (PreH4 : (i = (Zlength (l1_2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= numsSize_pre)) (PreH8 : (numsSize_pre <= 50000)) (PreH9 : (0 <= vote)) (PreH10 : (vote <= i)) (PreH11 : (IsMajorityElement x_2 l )) (PreH12 : (MajorityOnReduced x_2 candidate vote l2_2 )) ,
  (IntArray.full nums_pre numsSize_pre l )
|--
  EX (x: Z)  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ ((i + 1 ) = (Zlength (l1))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= (vote + 1 )) ” 
  &&  “ ((vote + 1 ) <= (i + 1 )) ” 
  &&  “ (IsMajorityElement x l ) ” 
  &&  “ (MajorityOnReduced x (Znth i l 0) (vote + 1 ) l2 ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (candidate: Z) (x_2: Z) (vote: Z) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (PreH1 : (vote = 0)) (PreH2 : (i < numsSize_pre)) (PreH3 : (l = (app (l1_2) (l2_2)))) (PreH4 : (i = (Zlength (l1_2)))) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= numsSize_pre)) (PreH8 : (numsSize_pre <= 50000)) (PreH9 : (0 <= vote)) (PreH10 : (vote <= i)) (PreH11 : (IsMajorityElement x_2 l )) (PreH12 : (MajorityOnReduced x_2 candidate vote l2_2 )) ,
  TT && emp 
|--
  EX (x: Z)  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ ((i + 1 ) = (Zlength (l1))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= (vote + 1 )) ” 
  &&  “ ((vote + 1 ) <= (i + 1 )) ” 
  &&  “ (IsMajorityElement x l ) ” 
  &&  “ (MajorityOnReduced x (Znth i l 0) (vote + 1 ) l2 ) ”
  &&  emp
).

Definition majorityElement_entail_wit_2_2 := 
(
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (candidate: Z) (x_2: Z) (vote: Z) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (PreH1 : ((Znth i l 0) = candidate)) (PreH2 : (vote <> 0)) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (app (l1_2) (l2_2)))) (PreH5 : (i = (Zlength (l1_2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : (0 <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x_2 l )) (PreH13 : (MajorityOnReduced x_2 candidate vote l2_2 )) ,
  (IntArray.full nums_pre numsSize_pre l )
|--
  EX (x: Z)  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ ((i + 1 ) = (Zlength (l1))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= (vote + 1 )) ” 
  &&  “ ((vote + 1 ) <= (i + 1 )) ” 
  &&  “ (IsMajorityElement x l ) ” 
  &&  “ (MajorityOnReduced x candidate (vote + 1 ) l2 ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (candidate: Z) (x_2: Z) (vote: Z) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (PreH1 : ((Znth i l 0) = candidate)) (PreH2 : (vote <> 0)) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (app (l1_2) (l2_2)))) (PreH5 : (i = (Zlength (l1_2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : (0 <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x_2 l )) (PreH13 : (MajorityOnReduced x_2 candidate vote l2_2 )) ,
  TT && emp 
|--
  EX (x: Z)  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ ((i + 1 ) = (Zlength (l1))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= (vote + 1 )) ” 
  &&  “ ((vote + 1 ) <= (i + 1 )) ” 
  &&  “ (IsMajorityElement x l ) ” 
  &&  “ (MajorityOnReduced x candidate (vote + 1 ) l2 ) ”
  &&  emp
).

Definition majorityElement_entail_wit_2_3 := 
(
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (candidate: Z) (x_2: Z) (vote: Z) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (PreH1 : ((Znth i l 0) <> candidate)) (PreH2 : (vote <> 0)) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (app (l1_2) (l2_2)))) (PreH5 : (i = (Zlength (l1_2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : (0 <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x_2 l )) (PreH13 : (MajorityOnReduced x_2 candidate vote l2_2 )) ,
  (IntArray.full nums_pre numsSize_pre l )
|--
  EX (x: Z)  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ ((i + 1 ) = (Zlength (l1))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= (vote + (-1) )) ” 
  &&  “ ((vote + (-1) ) <= (i + 1 )) ” 
  &&  “ (IsMajorityElement x l ) ” 
  &&  “ (MajorityOnReduced x candidate (vote + (-1) ) l2 ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (candidate: Z) (x_2: Z) (vote: Z) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (PreH1 : ((Znth i l 0) <> candidate)) (PreH2 : (vote <> 0)) (PreH3 : (i < numsSize_pre)) (PreH4 : (l = (app (l1_2) (l2_2)))) (PreH5 : (i = (Zlength (l1_2)))) (PreH6 : (0 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (1 <= numsSize_pre)) (PreH9 : (numsSize_pre <= 50000)) (PreH10 : (0 <= vote)) (PreH11 : (vote <= i)) (PreH12 : (IsMajorityElement x_2 l )) (PreH13 : (MajorityOnReduced x_2 candidate vote l2_2 )) ,
  TT && emp 
|--
  EX (x: Z)  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ ((i + 1 ) = (Zlength (l1))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= (vote + (-1) )) ” 
  &&  “ ((vote + (-1) ) <= (i + 1 )) ” 
  &&  “ (IsMajorityElement x l ) ” 
  &&  “ (MajorityOnReduced x candidate (vote + (-1) ) l2 ) ”
  &&  emp
).

Definition majorityElement_return_wit_1 := 
(
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (candidate: Z) (x: Z) (vote: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (i >= numsSize_pre)) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (i = (Zlength (l1)))) (PreH4 : (0 <= i)) (PreH5 : (i <= numsSize_pre)) (PreH6 : (1 <= numsSize_pre)) (PreH7 : (numsSize_pre <= 50000)) (PreH8 : (0 <= vote)) (PreH9 : (vote <= i)) (PreH10 : (IsMajorityElement x l )) (PreH11 : (MajorityOnReduced x candidate vote l2 )) ,
  (IntArray.full nums_pre numsSize_pre l )
|--
  “ (IsMajorityElement candidate l ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (candidate: Z) (x: Z) (vote: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (i >= numsSize_pre)) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (i = (Zlength (l1)))) (PreH4 : (0 <= i)) (PreH5 : (i <= numsSize_pre)) (PreH6 : (1 <= numsSize_pre)) (PreH7 : (numsSize_pre <= 50000)) (PreH8 : (0 <= vote)) (PreH9 : (vote <= i)) (PreH10 : (IsMajorityElement x l )) (PreH11 : (MajorityOnReduced x candidate vote l2 )) ,
  TT && emp 
|--
  “ (IsMajorityElement candidate l ) ”
  &&  emp
).

Definition majorityElement_return_wit_1_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (candidate: Z) (x: Z) (vote: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (i >= numsSize_pre)) (PreH2 : (l = (app (l1) (l2)))) (PreH3 : (i = (Zlength (l1)))) (PreH4 : (0 <= i)) (PreH5 : (i <= numsSize_pre)) (PreH6 : (1 <= numsSize_pre)) (PreH7 : (numsSize_pre <= 50000)) (PreH8 : (0 <= vote)) (PreH9 : (vote <= i)) (PreH10 : (IsMajorityElement x l )) (PreH11 : (MajorityOnReduced x candidate vote l2 )) ,
  (IsMajorityElement candidate l )
.

Definition majorityElement_partial_solve_wit_1 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (candidate: Z) (x: Z) (vote: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (vote = 0)) (PreH2 : (i < numsSize_pre)) (PreH3 : (l = (app (l1) (l2)))) (PreH4 : (i = (Zlength (l1)))) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= numsSize_pre)) (PreH8 : (numsSize_pre <= 50000)) (PreH9 : (0 <= vote)) (PreH10 : (vote <= i)) (PreH11 : (IsMajorityElement x l )) (PreH12 : (MajorityOnReduced x candidate vote l2 )) ,
  (IntArray.full nums_pre numsSize_pre l )
|--
  “ (vote = 0) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= vote) ” 
  &&  “ (vote <= i) ” 
  &&  “ (IsMajorityElement x l ) ” 
  &&  “ (MajorityOnReduced x candidate vote l2 ) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i nums_pre i 0 numsSize_pre l )
.

Definition majorityElement_partial_solve_wit_2 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (candidate: Z) (x: Z) (vote: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (vote = 0)) (PreH2 : (i < numsSize_pre)) (PreH3 : (l = (app (l1) (l2)))) (PreH4 : (i = (Zlength (l1)))) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= numsSize_pre)) (PreH8 : (numsSize_pre <= 50000)) (PreH9 : (0 <= vote)) (PreH10 : (vote <= i)) (PreH11 : (IsMajorityElement x l )) (PreH12 : (MajorityOnReduced x candidate vote l2 )) ,
  (IntArray.full nums_pre numsSize_pre l )
|--
  “ (vote = 0) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= vote) ” 
  &&  “ (vote <= i) ” 
  &&  “ (IsMajorityElement x l ) ” 
  &&  “ (MajorityOnReduced x candidate vote l2 ) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i nums_pre i 0 numsSize_pre l )
.

Definition majorityElement_partial_solve_wit_3 := 
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (candidate: Z) (x: Z) (vote: Z) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (vote <> 0)) (PreH2 : (i < numsSize_pre)) (PreH3 : (l = (app (l1) (l2)))) (PreH4 : (i = (Zlength (l1)))) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= numsSize_pre)) (PreH8 : (numsSize_pre <= 50000)) (PreH9 : (0 <= vote)) (PreH10 : (vote <= i)) (PreH11 : (IsMajorityElement x l )) (PreH12 : (MajorityOnReduced x candidate vote l2 )) ,
  (IntArray.full nums_pre numsSize_pre l )
|--
  “ (vote <> 0) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (0 <= vote) ” 
  &&  “ (vote <= i) ” 
  &&  “ (IsMajorityElement x l ) ” 
  &&  “ (MajorityOnReduced x candidate vote l2 ) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i nums_pre i 0 numsSize_pre l )
.

Module Type VC_Correct.


Axiom proof_of_majorityElement_safety_wit_1 : majorityElement_safety_wit_1.
Axiom proof_of_majorityElement_safety_wit_2 : majorityElement_safety_wit_2.
Axiom proof_of_majorityElement_safety_wit_3 : majorityElement_safety_wit_3.
Axiom proof_of_majorityElement_safety_wit_4 : majorityElement_safety_wit_4.
Axiom proof_of_majorityElement_safety_wit_5 : majorityElement_safety_wit_5.
Axiom proof_of_majorityElement_safety_wit_6 : majorityElement_safety_wit_6.
Axiom proof_of_majorityElement_safety_wit_7 : majorityElement_safety_wit_7.
Axiom proof_of_majorityElement_safety_wit_8 : majorityElement_safety_wit_8.
Axiom proof_of_majorityElement_safety_wit_9 : majorityElement_safety_wit_9.
Axiom proof_of_majorityElement_safety_wit_10 : majorityElement_safety_wit_10.
Axiom proof_of_majorityElement_safety_wit_11 : majorityElement_safety_wit_11.
Axiom proof_of_majorityElement_safety_wit_12 : majorityElement_safety_wit_12.
Axiom proof_of_majorityElement_safety_wit_13 : majorityElement_safety_wit_13.
Axiom proof_of_majorityElement_safety_wit_14 : majorityElement_safety_wit_14.
Axiom proof_of_majorityElement_entail_wit_1 : majorityElement_entail_wit_1.
Axiom proof_of_majorityElement_entail_wit_2_1 : majorityElement_entail_wit_2_1.
Axiom proof_of_majorityElement_entail_wit_2_2 : majorityElement_entail_wit_2_2.
Axiom proof_of_majorityElement_entail_wit_2_3 : majorityElement_entail_wit_2_3.
Axiom proof_of_majorityElement_return_wit_1 : majorityElement_return_wit_1.
Axiom proof_of_majorityElement_partial_solve_wit_1 : majorityElement_partial_solve_wit_1.
Axiom proof_of_majorityElement_partial_solve_wit_2 : majorityElement_partial_solve_wit_2.
Axiom proof_of_majorityElement_partial_solve_wit_3 : majorityElement_partial_solve_wit_3.

End VC_Correct.
