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
Require Import SimpleC.EE.QCP_demos_LLM.sortArray_lib.
Local Open Scope sac.

(*----- Function sortArray -----*)

Definition sortArray_safety_wit_1 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sortArray_safety_wit_2 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (app (l1) (l2)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l1)))) (PreH7 : (0 <= i)) (PreH8 : (i <= numsSize_pre)) (PreH9 : (Permutation l l3 )) (PreH10 : (increasing l1 )) (PreH11 : (prefix_suffix_sorted l1 l2 )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sortArray_safety_wit_3 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (app (l1) (l2)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l1)))) (PreH7 : (0 <= i)) (PreH8 : (i <= numsSize_pre)) (PreH9 : (Permutation l l3 )) (PreH10 : (increasing l1 )) (PreH11 : (prefix_suffix_sorted l1 l2 )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sortArray_safety_wit_4 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth j l3 0) < (Znth i l3 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = (app (l1) ((app ((cons (key) (l2))) (l4)))))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (j = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= numsSize_pre)) (PreH13 : (Permutation l l3 )) (PreH14 : (increasing l1 )) (PreH15 : (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) )) (PreH16 : (lowerbound key l2 )) ,
  (IntArray.full nums_pre numsSize_pre (replace_Znth (j) ((Znth i l3 0)) ((replace_Znth (i) ((Znth j l3 0)) (l3)))) )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sortArray_safety_wit_5 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth j l3 0) >= (Znth i l3 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = (app (l1) ((app ((cons (key) (l2))) (l4)))))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (j = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= numsSize_pre)) (PreH13 : (Permutation l l3 )) (PreH14 : (increasing l1 )) (PreH15 : (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) )) (PreH16 : (lowerbound key l2 )) ,
  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sortArray_safety_wit_6 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : (j >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (app (l1) ((app ((cons (key) (l2))) (l4)))))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l1)))) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (j = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH10 : ((i + 1 ) <= j)) (PreH11 : (j <= numsSize_pre)) (PreH12 : (Permutation l l3 )) (PreH13 : (increasing l1 )) (PreH14 : (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) )) (PreH15 : (lowerbound key l2 )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sortArray_entail_wit_1 := 
(
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app (l1) (l2))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (0 = (Zlength (l1))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ (prefix_suffix_sorted l1 l2 ) ”
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) ,
  TT && emp 
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (0 = (Zlength (l1))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (Permutation l (app (l1) (l2)) ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ (prefix_suffix_sorted l1 l2 ) ”
  &&  emp
).

Definition sortArray_entail_wit_2 := 
(
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3_2 = (app (l1_2) (l2_2)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l1_2)))) (PreH7 : (0 <= i)) (PreH8 : (i <= numsSize_pre)) (PreH9 : (Permutation l l3_2 )) (PreH10 : (increasing l1_2 )) (PreH11 : (prefix_suffix_sorted l1_2 l2_2 )) ,
  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3_2 )
|--
  EX (l1: (@list Z))  (key: Z)  (l2: (@list Z))  (l4: (@list Z))  (l3: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app (l1) ((app ((cons (key) (l2))) (l4))))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ ((i + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) ) ” 
  &&  “ (lowerbound key l2 ) ”
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3_2 = (app (l1_2) (l2_2)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l1_2)))) (PreH7 : (0 <= i)) (PreH8 : (i <= numsSize_pre)) (PreH9 : (Permutation l l3_2 )) (PreH10 : (increasing l1_2 )) (PreH11 : (prefix_suffix_sorted l1_2 l2_2 )) ,
  TT && emp 
|--
  EX (l1: (@list Z))  (key: Z)  (l2: (@list Z))  (l4: (@list Z)) ,
  “ (l3_2 = (app (l1) ((app ((cons (key) (l2))) (l4))))) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ ((i + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (Permutation l (app (l1) ((app ((cons (key) (l2))) (l4)))) ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) ) ” 
  &&  “ (lowerbound key l2 ) ”
  &&  emp
).

Definition sortArray_entail_wit_3_1 := 
(
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1_2: (@list Z)) (key_2: Z) (l2_2: (@list Z)) (l4_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : ((Znth j l3_2 0) < (Znth i l3_2 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3_2 = (app (l1_2) ((app ((cons (key_2) (l2_2))) (l4_2)))))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1_2)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (j = (Zlength ((app (l1_2) ((cons (key_2) (l2_2)))))))) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= numsSize_pre)) (PreH13 : (Permutation l l3_2 )) (PreH14 : (increasing l1_2 )) (PreH15 : (prefix_suffix_sorted l1_2 (app ((cons (key_2) (l2_2))) (l4_2)) )) (PreH16 : (lowerbound key_2 l2_2 )) ,
  (IntArray.full nums_pre numsSize_pre (replace_Znth (j) ((Znth i l3_2 0)) ((replace_Znth (i) ((Znth j l3_2 0)) (l3_2)))) )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  EX (l1: (@list Z))  (key: Z)  (l2: (@list Z))  (l4: (@list Z))  (l3: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app (l1) ((app ((cons (key) (l2))) (l4))))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((j + 1 ) = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ ((i + 1 ) <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= numsSize_pre) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) ) ” 
  &&  “ (lowerbound key l2 ) ”
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1_2: (@list Z)) (key_2: Z) (l2_2: (@list Z)) (l4_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : ((Znth j l3_2 0) < (Znth i l3_2 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3_2 = (app (l1_2) ((app ((cons (key_2) (l2_2))) (l4_2)))))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1_2)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (j = (Zlength ((app (l1_2) ((cons (key_2) (l2_2)))))))) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= numsSize_pre)) (PreH13 : (Permutation l l3_2 )) (PreH14 : (increasing l1_2 )) (PreH15 : (prefix_suffix_sorted l1_2 (app ((cons (key_2) (l2_2))) (l4_2)) )) (PreH16 : (lowerbound key_2 l2_2 )) ,
  TT && emp 
|--
  EX (l1: (@list Z))  (key: Z)  (l2: (@list Z))  (l4: (@list Z)) ,
  “ ((replace_Znth (j) ((Znth i l3_2 0)) ((replace_Znth (i) ((Znth j l3_2 0)) (l3_2)))) = (app (l1) ((app ((cons (key) (l2))) (l4))))) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((j + 1 ) = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ ((i + 1 ) <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= numsSize_pre) ” 
  &&  “ (Permutation l (app (l1) ((app ((cons (key) (l2))) (l4)))) ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) ) ” 
  &&  “ (lowerbound key l2 ) ”
  &&  emp
).

Definition sortArray_entail_wit_3_2 := 
(
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1_2: (@list Z)) (key_2: Z) (l2_2: (@list Z)) (l4_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : ((Znth j l3_2 0) >= (Znth i l3_2 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3_2 = (app (l1_2) ((app ((cons (key_2) (l2_2))) (l4_2)))))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1_2)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (j = (Zlength ((app (l1_2) ((cons (key_2) (l2_2)))))))) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= numsSize_pre)) (PreH13 : (Permutation l l3_2 )) (PreH14 : (increasing l1_2 )) (PreH15 : (prefix_suffix_sorted l1_2 (app ((cons (key_2) (l2_2))) (l4_2)) )) (PreH16 : (lowerbound key_2 l2_2 )) ,
  (IntArray.full nums_pre numsSize_pre l3_2 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  EX (l1: (@list Z))  (key: Z)  (l2: (@list Z))  (l4: (@list Z))  (l3: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app (l1) ((app ((cons (key) (l2))) (l4))))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((j + 1 ) = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ ((i + 1 ) <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= numsSize_pre) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) ) ” 
  &&  “ (lowerbound key l2 ) ”
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1_2: (@list Z)) (key_2: Z) (l2_2: (@list Z)) (l4_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : ((Znth j l3_2 0) >= (Znth i l3_2 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3_2 = (app (l1_2) ((app ((cons (key_2) (l2_2))) (l4_2)))))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1_2)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (j = (Zlength ((app (l1_2) ((cons (key_2) (l2_2)))))))) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= numsSize_pre)) (PreH13 : (Permutation l l3_2 )) (PreH14 : (increasing l1_2 )) (PreH15 : (prefix_suffix_sorted l1_2 (app ((cons (key_2) (l2_2))) (l4_2)) )) (PreH16 : (lowerbound key_2 l2_2 )) ,
  TT && emp 
|--
  EX (l1: (@list Z))  (key: Z)  (l2: (@list Z))  (l4: (@list Z)) ,
  “ (l3_2 = (app (l1) ((app ((cons (key) (l2))) (l4))))) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((j + 1 ) = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ ((i + 1 ) <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= numsSize_pre) ” 
  &&  “ (Permutation l (app (l1) ((app ((cons (key) (l2))) (l4)))) ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) ) ” 
  &&  “ (lowerbound key l2 ) ”
  &&  emp
).

Definition sortArray_entail_wit_4 := 
(
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1_2: (@list Z)) (key: Z) (l2_2: (@list Z)) (l4: (@list Z)) (l3_2: (@list Z)) (PreH1 : (j >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3_2 = (app (l1_2) ((app ((cons (key) (l2_2))) (l4)))))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l1_2)))) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (j = (Zlength ((app (l1_2) ((cons (key) (l2_2)))))))) (PreH10 : ((i + 1 ) <= j)) (PreH11 : (j <= numsSize_pre)) (PreH12 : (Permutation l l3_2 )) (PreH13 : (increasing l1_2 )) (PreH14 : (prefix_suffix_sorted l1_2 (app ((cons (key) (l2_2))) (l4)) )) (PreH15 : (lowerbound key l2_2 )) ,
  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app (l1) (l2))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ ((i + 1 ) = (Zlength (l1))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ (prefix_suffix_sorted l1 l2 ) ”
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1_2: (@list Z)) (key: Z) (l2_2: (@list Z)) (l4: (@list Z)) (l3_2: (@list Z)) (PreH1 : (j >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3_2 = (app (l1_2) ((app ((cons (key) (l2_2))) (l4)))))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l1_2)))) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (j = (Zlength ((app (l1_2) ((cons (key) (l2_2)))))))) (PreH10 : ((i + 1 ) <= j)) (PreH11 : (j <= numsSize_pre)) (PreH12 : (Permutation l l3_2 )) (PreH13 : (increasing l1_2 )) (PreH14 : (prefix_suffix_sorted l1_2 (app ((cons (key) (l2_2))) (l4)) )) (PreH15 : (lowerbound key l2_2 )) ,
  TT && emp 
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l3_2 = (app (l1) (l2))) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ ((i + 1 ) = (Zlength (l1))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (Permutation l (app (l1) (l2)) ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ (prefix_suffix_sorted l1 l2 ) ”
  &&  emp
).

Definition sortArray_return_wit_1 := 
(
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (i: Z) (l1_2: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (app (l1_2) (l2)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l1_2)))) (PreH7 : (0 <= i)) (PreH8 : (i <= numsSize_pre)) (PreH9 : (Permutation l l3 )) (PreH10 : (increasing l1_2 )) (PreH11 : (prefix_suffix_sorted l1_2 l2 )) ,
  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ ((Zlength (l1)) = numsSize_pre) ”
  &&  (IntArray.full nums_pre numsSize_pre l1 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (i: Z) (l1_2: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (app (l1_2) (l2)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l1_2)))) (PreH7 : (0 <= i)) (PreH8 : (i <= numsSize_pre)) (PreH9 : (Permutation l l3 )) (PreH10 : (increasing l1_2 )) (PreH11 : (prefix_suffix_sorted l1_2 l2 )) ,
  TT && emp 
|--
  “ ((Zlength (l3)) = numsSize_pre) ” 
  &&  “ (increasing l3 ) ”
  &&  emp
).

Definition sortArray_return_wit_1_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (i: Z) (l1_2: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (app (l1_2) (l2)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l1_2)))) (PreH7 : (0 <= i)) (PreH8 : (i <= numsSize_pre)) (PreH9 : (Permutation l l3 )) (PreH10 : (increasing l1_2 )) (PreH11 : (prefix_suffix_sorted l1_2 l2 )) ,
  ((Zlength (l3)) = numsSize_pre)
.

Definition sortArray_return_wit_1_split_goal_2 := 
forall (numsSize_pre: Z) (l: (@list Z)) (i: Z) (l1_2: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (app (l1_2) (l2)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l1_2)))) (PreH7 : (0 <= i)) (PreH8 : (i <= numsSize_pre)) (PreH9 : (Permutation l l3 )) (PreH10 : (increasing l1_2 )) (PreH11 : (prefix_suffix_sorted l1_2 l2 )) ,
  (increasing l3 )
.

Definition sortArray_partial_solve_wit_1 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : (j < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (app (l1) ((app ((cons (key) (l2))) (l4)))))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l1)))) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (j = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH10 : ((i + 1 ) <= j)) (PreH11 : (j <= numsSize_pre)) (PreH12 : (Permutation l l3 )) (PreH13 : (increasing l1 )) (PreH14 : (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) )) (PreH15 : (lowerbound key l2 )) ,
  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  “ (j < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app (l1) ((app ((cons (key) (l2))) (l4))))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (j = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) ) ” 
  &&  “ (lowerbound key l2 ) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int  |-> (Znth j l3 0))
  **  (IntArray.missing_i nums_pre j 0 numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Definition sortArray_partial_solve_wit_2 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : (j < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (app (l1) ((app ((cons (key) (l2))) (l4)))))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l1)))) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (j = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH10 : ((i + 1 ) <= j)) (PreH11 : (j <= numsSize_pre)) (PreH12 : (Permutation l l3 )) (PreH13 : (increasing l1 )) (PreH14 : (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) )) (PreH15 : (lowerbound key l2 )) ,
  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  “ (j < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app (l1) ((app ((cons (key) (l2))) (l4))))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (j = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) ) ” 
  &&  “ (lowerbound key l2 ) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l3 0))
  **  (IntArray.missing_i nums_pre i 0 numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Definition sortArray_partial_solve_wit_3 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth j l3 0) < (Znth i l3 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = (app (l1) ((app ((cons (key) (l2))) (l4)))))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (j = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= numsSize_pre)) (PreH13 : (Permutation l l3 )) (PreH14 : (increasing l1 )) (PreH15 : (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) )) (PreH16 : (lowerbound key l2 )) ,
  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  “ ((Znth j l3 0) < (Znth i l3 0)) ” 
  &&  “ (j < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app (l1) ((app ((cons (key) (l2))) (l4))))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (j = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) ) ” 
  &&  “ (lowerbound key l2 ) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l3 0))
  **  (IntArray.missing_i nums_pre i 0 numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Definition sortArray_partial_solve_wit_4 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth j l3 0) < (Znth i l3 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = (app (l1) ((app ((cons (key) (l2))) (l4)))))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (j = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= numsSize_pre)) (PreH13 : (Permutation l l3 )) (PreH14 : (increasing l1 )) (PreH15 : (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) )) (PreH16 : (lowerbound key l2 )) ,
  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  “ ((Znth j l3 0) < (Znth i l3 0)) ” 
  &&  “ (j < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app (l1) ((app ((cons (key) (l2))) (l4))))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (j = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) ) ” 
  &&  “ (lowerbound key l2 ) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int  |-> (Znth j l3 0))
  **  (IntArray.missing_i nums_pre j 0 numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Definition sortArray_partial_solve_wit_5 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth j l3 0) < (Znth i l3 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = (app (l1) ((app ((cons (key) (l2))) (l4)))))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (j = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= numsSize_pre)) (PreH13 : (Permutation l l3 )) (PreH14 : (increasing l1 )) (PreH15 : (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) )) (PreH16 : (lowerbound key l2 )) ,
  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  “ ((Znth j l3 0) < (Znth i l3 0)) ” 
  &&  “ (j < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app (l1) ((app ((cons (key) (l2))) (l4))))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (j = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) ) ” 
  &&  “ (lowerbound key l2 ) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre i 0 numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Definition sortArray_partial_solve_wit_6 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth j l3 0) < (Znth i l3 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = (app (l1) ((app ((cons (key) (l2))) (l4)))))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (j = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= numsSize_pre)) (PreH13 : (Permutation l l3 )) (PreH14 : (increasing l1 )) (PreH15 : (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) )) (PreH16 : (lowerbound key l2 )) ,
  (IntArray.full nums_pre numsSize_pre (replace_Znth (i) ((Znth j l3 0)) (l3)) )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  “ ((Znth j l3 0) < (Znth i l3 0)) ” 
  &&  “ (j < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app (l1) ((app ((cons (key) (l2))) (l4))))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (j = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ (prefix_suffix_sorted l1 (app ((cons (key) (l2))) (l4)) ) ” 
  &&  “ (lowerbound key l2 ) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre j 0 numsSize_pre (replace_Znth (i) ((Znth j l3 0)) (l3)) )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Module Type VC_Correct.


Axiom proof_of_sortArray_safety_wit_1 : sortArray_safety_wit_1.
Axiom proof_of_sortArray_safety_wit_2 : sortArray_safety_wit_2.
Axiom proof_of_sortArray_safety_wit_3 : sortArray_safety_wit_3.
Axiom proof_of_sortArray_safety_wit_4 : sortArray_safety_wit_4.
Axiom proof_of_sortArray_safety_wit_5 : sortArray_safety_wit_5.
Axiom proof_of_sortArray_safety_wit_6 : sortArray_safety_wit_6.
Axiom proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1.
Axiom proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2.
Axiom proof_of_sortArray_entail_wit_3_1 : sortArray_entail_wit_3_1.
Axiom proof_of_sortArray_entail_wit_3_2 : sortArray_entail_wit_3_2.
Axiom proof_of_sortArray_entail_wit_4 : sortArray_entail_wit_4.
Axiom proof_of_sortArray_return_wit_1 : sortArray_return_wit_1.
Axiom proof_of_sortArray_partial_solve_wit_1 : sortArray_partial_solve_wit_1.
Axiom proof_of_sortArray_partial_solve_wit_2 : sortArray_partial_solve_wit_2.
Axiom proof_of_sortArray_partial_solve_wit_3 : sortArray_partial_solve_wit_3.
Axiom proof_of_sortArray_partial_solve_wit_4 : sortArray_partial_solve_wit_4.
Axiom proof_of_sortArray_partial_solve_wit_5 : sortArray_partial_solve_wit_5.
Axiom proof_of_sortArray_partial_solve_wit_6 : sortArray_partial_solve_wit_6.

End VC_Correct.
