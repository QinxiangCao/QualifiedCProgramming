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
  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sortArray_safety_wit_2 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (numsSize_pre > 1)) (PreH2 : ((Zlength (l)) = numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) ,
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

Definition sortArray_safety_wit_3 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 50000)) (PreH3 : (l3 = (app (l1) (l2)))) (PreH4 : (numsSize_pre = (Zlength (l)))) (PreH5 : (i = (Zlength (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (1 <= (Zlength (l1)))) (PreH9 : (Permutation l l3 )) (PreH10 : (increasing l2 )) (PreH11 : (prefix_suffix_sorted l1 l2 )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  “ ((numsSize_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (numsSize_pre - 1 )) ”
.

Definition sortArray_safety_wit_4 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 50000)) (PreH3 : (l3 = (app (l1) (l2)))) (PreH4 : (numsSize_pre = (Zlength (l)))) (PreH5 : (i = (Zlength (l2)))) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (1 <= (Zlength (l1)))) (PreH9 : (Permutation l l3 )) (PreH10 : (increasing l2 )) (PreH11 : (prefix_suffix_sorted l1 l2 )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sortArray_safety_wit_5 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (i < (numsSize_pre - 1 ))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (app (l1) (l2)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l2)))) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (1 <= (Zlength (l1)))) (PreH10 : (Permutation l l3 )) (PreH11 : (increasing l2 )) (PreH12 : (prefix_suffix_sorted l1 l2 )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sortArray_safety_wit_6 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 50000)) (PreH3 : (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4)))) (PreH4 : (numsSize_pre = (Zlength (l)))) (PreH5 : (i = (Zlength (l4)))) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (i < (numsSize_pre - 1 ))) (PreH9 : (j = (Zlength (l1)))) (PreH10 : (0 <= j)) (PreH11 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH12 : ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH13 : (Permutation l l3 )) (PreH14 : (increasing l4 )) (PreH15 : (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 )) (PreH16 : (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  “ ((numsSize_pre - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (numsSize_pre - i )) ”
.

Definition sortArray_safety_wit_7 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 50000)) (PreH3 : (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4)))) (PreH4 : (numsSize_pre = (Zlength (l)))) (PreH5 : (i = (Zlength (l4)))) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (i < (numsSize_pre - 1 ))) (PreH9 : (j = (Zlength (l1)))) (PreH10 : (0 <= j)) (PreH11 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH12 : ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH13 : (Permutation l l3 )) (PreH14 : (increasing l4 )) (PreH15 : (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 )) (PreH16 : (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sortArray_safety_wit_8 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 50000)) (PreH3 : (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4)))) (PreH4 : (numsSize_pre = (Zlength (l)))) (PreH5 : (i = (Zlength (l4)))) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (i < (numsSize_pre - 1 ))) (PreH9 : (j = (Zlength (l1)))) (PreH10 : (0 <= j)) (PreH11 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH12 : ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH13 : (Permutation l l3 )) (PreH14 : (increasing l4 )) (PreH15 : (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 )) (PreH16 : (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sortArray_safety_wit_9 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((j + 1 ) < (numsSize_pre - i ))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l4)))) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (i < (numsSize_pre - 1 ))) (PreH10 : (j = (Zlength (l1)))) (PreH11 : (0 <= j)) (PreH12 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH13 : ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH14 : (Permutation l l3 )) (PreH15 : (increasing l4 )) (PreH16 : (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 )) (PreH17 : (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) )) ,
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

Definition sortArray_safety_wit_10 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((j + 1 ) < (numsSize_pre - i ))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l4)))) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (i < (numsSize_pre - 1 ))) (PreH10 : (j = (Zlength (l1)))) (PreH11 : (0 <= j)) (PreH12 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH13 : ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH14 : (Permutation l l3 )) (PreH15 : (increasing l4 )) (PreH16 : (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 )) (PreH17 : (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) )) ,
  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sortArray_safety_wit_11 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth j l3 0) > (Znth (j + 1 ) l3 0))) (PreH2 : ((j + 1 ) < (numsSize_pre - i ))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1 ))) (PreH11 : (j = (Zlength (l1)))) (PreH12 : (0 <= j)) (PreH13 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH14 : ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH15 : (Permutation l l3 )) (PreH16 : (increasing l4 )) (PreH17 : (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 )) (PreH18 : (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) )) ,
  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth j l3 0))
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

Definition sortArray_safety_wit_12 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth j l3 0) > (Znth (j + 1 ) l3 0))) (PreH2 : ((j + 1 ) < (numsSize_pre - i ))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1 ))) (PreH11 : (j = (Zlength (l1)))) (PreH12 : (0 <= j)) (PreH13 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH14 : ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH15 : (Permutation l l3 )) (PreH16 : (increasing l4 )) (PreH17 : (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 )) (PreH18 : (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) )) ,
  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth j l3 0))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sortArray_safety_wit_13 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth j l3 0) > (Znth (j + 1 ) l3 0))) (PreH2 : ((j + 1 ) < (numsSize_pre - i ))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1 ))) (PreH11 : (j = (Zlength (l1)))) (PreH12 : (0 <= j)) (PreH13 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH14 : ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH15 : (Permutation l l3 )) (PreH16 : (increasing l4 )) (PreH17 : (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 )) (PreH18 : (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) )) ,
  (IntArray.full nums_pre numsSize_pre (replace_Znth (j) ((Znth (j + 1 ) l3 0)) (l3)) )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth j l3 0))
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

Definition sortArray_safety_wit_14 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth j l3 0) > (Znth (j + 1 ) l3 0))) (PreH2 : ((j + 1 ) < (numsSize_pre - i ))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1 ))) (PreH11 : (j = (Zlength (l1)))) (PreH12 : (0 <= j)) (PreH13 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH14 : ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH15 : (Permutation l l3 )) (PreH16 : (increasing l4 )) (PreH17 : (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 )) (PreH18 : (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) )) ,
  (IntArray.full nums_pre numsSize_pre (replace_Znth (j) ((Znth (j + 1 ) l3 0)) (l3)) )
  **  ((( &( "tmp" ) )) # Int  |-> (Znth j l3 0))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sortArray_safety_wit_15 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth j l3 0) > (Znth (j + 1 ) l3 0))) (PreH2 : ((j + 1 ) < (numsSize_pre - i ))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1 ))) (PreH11 : (j = (Zlength (l1)))) (PreH12 : (0 <= j)) (PreH13 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH14 : ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH15 : (Permutation l l3 )) (PreH16 : (increasing l4 )) (PreH17 : (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 )) (PreH18 : (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) )) ,
  (IntArray.full nums_pre numsSize_pre (replace_Znth ((j + 1 )) ((Znth j l3 0)) ((replace_Znth (j) ((Znth (j + 1 ) l3 0)) (l3)))) )
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

Definition sortArray_safety_wit_16 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth j l3 0) <= (Znth (j + 1 ) l3 0))) (PreH2 : ((j + 1 ) < (numsSize_pre - i ))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1 ))) (PreH11 : (j = (Zlength (l1)))) (PreH12 : (0 <= j)) (PreH13 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH14 : ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH15 : (Permutation l l3 )) (PreH16 : (increasing l4 )) (PreH17 : (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 )) (PreH18 : (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) )) ,
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

Definition sortArray_safety_wit_17 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((j + 1 ) >= (numsSize_pre - i ))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l4)))) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (i < (numsSize_pre - 1 ))) (PreH10 : (j = (Zlength (l1)))) (PreH11 : (0 <= j)) (PreH12 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH13 : ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH14 : (Permutation l l3 )) (PreH15 : (increasing l4 )) (PreH16 : (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 )) (PreH17 : (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) )) ,
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
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (numsSize_pre > 1)) (PreH2 : ((Zlength (l)) = numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app (l1) (l2))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (0 = (Zlength (l2))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < numsSize_pre) ” 
  &&  “ (1 <= (Zlength (l1))) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l2 ) ” 
  &&  “ (prefix_suffix_sorted l1 l2 ) ”
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (PreH1 : (numsSize_pre > 1)) (PreH2 : ((Zlength (l)) = numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) ,
  TT && emp 
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (0 = (Zlength (l2))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < numsSize_pre) ” 
  &&  “ (1 <= (Zlength (l1))) ” 
  &&  “ (Permutation l (app (l1) (l2)) ) ” 
  &&  “ (increasing l2 ) ” 
  &&  “ (prefix_suffix_sorted l1 l2 ) ”
  &&  emp
).

Definition sortArray_entail_wit_2 := 
(
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (i < (numsSize_pre - 1 ))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3_2 = (app (l1_2) (l2_2)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l2_2)))) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (1 <= (Zlength (l1_2)))) (PreH10 : (Permutation l l3_2 )) (PreH11 : (increasing l2_2 )) (PreH12 : (prefix_suffix_sorted l1_2 l2_2 )) ,
  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3_2 )
|--
  EX (l1: (@list Z))  (key: Z)  (l2: (@list Z))  (l4: (@list Z))  (l3: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l4))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (i < (numsSize_pre - 1 )) ” 
  &&  “ (0 = (Zlength (l1))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((0 + 1 ) <= (numsSize_pre - i )) ” 
  &&  “ ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l4 ) ” 
  &&  “ (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) ” 
  &&  “ (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) ) ”
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (i: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (i < (numsSize_pre - 1 ))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3_2 = (app (l1_2) (l2_2)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l2_2)))) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (1 <= (Zlength (l1_2)))) (PreH10 : (Permutation l l3_2 )) (PreH11 : (increasing l2_2 )) (PreH12 : (prefix_suffix_sorted l1_2 l2_2 )) ,
  TT && emp 
|--
  EX (l1: (@list Z))  (key: Z)  (l2: (@list Z))  (l4: (@list Z)) ,
  “ (l3_2 = (app ((app (l1) ((cons (key) (l2))))) (l4))) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l4))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (i < (numsSize_pre - 1 )) ” 
  &&  “ (0 = (Zlength (l1))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((0 + 1 ) <= (numsSize_pre - i )) ” 
  &&  “ ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ (Permutation l (app ((app (l1) ((cons (key) (l2))))) (l4)) ) ” 
  &&  “ (increasing l4 ) ” 
  &&  “ (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) ” 
  &&  “ (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) ) ”
  &&  emp
).

Definition sortArray_entail_wit_3_1 := 
(
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1_2: (@list Z)) (key_2: Z) (l2_2: (@list Z)) (l4_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : ((Znth j l3_2 0) > (Znth (j + 1 ) l3_2 0))) (PreH2 : ((j + 1 ) < (numsSize_pre - i ))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3_2 = (app ((app (l1_2) ((cons (key_2) (l2_2))))) (l4_2)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4_2)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1 ))) (PreH11 : (j = (Zlength (l1_2)))) (PreH12 : (0 <= j)) (PreH13 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH14 : ((numsSize_pre - i ) = (Zlength ((app (l1_2) ((cons (key_2) (l2_2)))))))) (PreH15 : (Permutation l l3_2 )) (PreH16 : (increasing l4_2 )) (PreH17 : (prefix_suffix_sorted (app (l1_2) ((cons (key_2) (l2_2)))) l4_2 )) (PreH18 : (prefix_suffix_sorted l1_2 (cons (key_2) ((@nil Z))) )) ,
  (IntArray.full nums_pre numsSize_pre (replace_Znth ((j + 1 )) ((Znth j l3_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) l3_2 0)) (l3_2)))) )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  EX (l1: (@list Z))  (key: Z)  (l2: (@list Z))  (l4: (@list Z))  (l3: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l4))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (i < (numsSize_pre - 1 )) ” 
  &&  “ ((j + 1 ) = (Zlength (l1))) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ (((j + 1 ) + 1 ) <= (numsSize_pre - i )) ” 
  &&  “ ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l4 ) ” 
  &&  “ (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) ” 
  &&  “ (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) ) ”
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1_2: (@list Z)) (key_2: Z) (l2_2: (@list Z)) (l4_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : ((Znth j l3_2 0) > (Znth (j + 1 ) l3_2 0))) (PreH2 : ((j + 1 ) < (numsSize_pre - i ))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3_2 = (app ((app (l1_2) ((cons (key_2) (l2_2))))) (l4_2)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4_2)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1 ))) (PreH11 : (j = (Zlength (l1_2)))) (PreH12 : (0 <= j)) (PreH13 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH14 : ((numsSize_pre - i ) = (Zlength ((app (l1_2) ((cons (key_2) (l2_2)))))))) (PreH15 : (Permutation l l3_2 )) (PreH16 : (increasing l4_2 )) (PreH17 : (prefix_suffix_sorted (app (l1_2) ((cons (key_2) (l2_2)))) l4_2 )) (PreH18 : (prefix_suffix_sorted l1_2 (cons (key_2) ((@nil Z))) )) ,
  TT && emp 
|--
  EX (l1: (@list Z))  (key: Z)  (l2: (@list Z))  (l4: (@list Z)) ,
  “ ((replace_Znth ((j + 1 )) ((Znth j l3_2 0)) ((replace_Znth (j) ((Znth (j + 1 ) l3_2 0)) (l3_2)))) = (app ((app (l1) ((cons (key) (l2))))) (l4))) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l4))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (i < (numsSize_pre - 1 )) ” 
  &&  “ ((j + 1 ) = (Zlength (l1))) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ (((j + 1 ) + 1 ) <= (numsSize_pre - i )) ” 
  &&  “ ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ (Permutation l (app ((app (l1) ((cons (key) (l2))))) (l4)) ) ” 
  &&  “ (increasing l4 ) ” 
  &&  “ (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) ” 
  &&  “ (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) ) ”
  &&  emp
).

Definition sortArray_entail_wit_3_2 := 
(
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1_2: (@list Z)) (key_2: Z) (l2_2: (@list Z)) (l4_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : ((Znth j l3_2 0) <= (Znth (j + 1 ) l3_2 0))) (PreH2 : ((j + 1 ) < (numsSize_pre - i ))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3_2 = (app ((app (l1_2) ((cons (key_2) (l2_2))))) (l4_2)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4_2)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1 ))) (PreH11 : (j = (Zlength (l1_2)))) (PreH12 : (0 <= j)) (PreH13 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH14 : ((numsSize_pre - i ) = (Zlength ((app (l1_2) ((cons (key_2) (l2_2)))))))) (PreH15 : (Permutation l l3_2 )) (PreH16 : (increasing l4_2 )) (PreH17 : (prefix_suffix_sorted (app (l1_2) ((cons (key_2) (l2_2)))) l4_2 )) (PreH18 : (prefix_suffix_sorted l1_2 (cons (key_2) ((@nil Z))) )) ,
  (IntArray.full nums_pre numsSize_pre l3_2 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  EX (l1: (@list Z))  (key: Z)  (l2: (@list Z))  (l4: (@list Z))  (l3: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l4))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (i < (numsSize_pre - 1 )) ” 
  &&  “ ((j + 1 ) = (Zlength (l1))) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ (((j + 1 ) + 1 ) <= (numsSize_pre - i )) ” 
  &&  “ ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l4 ) ” 
  &&  “ (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) ” 
  &&  “ (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) ) ”
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1_2: (@list Z)) (key_2: Z) (l2_2: (@list Z)) (l4_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : ((Znth j l3_2 0) <= (Znth (j + 1 ) l3_2 0))) (PreH2 : ((j + 1 ) < (numsSize_pre - i ))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3_2 = (app ((app (l1_2) ((cons (key_2) (l2_2))))) (l4_2)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4_2)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1 ))) (PreH11 : (j = (Zlength (l1_2)))) (PreH12 : (0 <= j)) (PreH13 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH14 : ((numsSize_pre - i ) = (Zlength ((app (l1_2) ((cons (key_2) (l2_2)))))))) (PreH15 : (Permutation l l3_2 )) (PreH16 : (increasing l4_2 )) (PreH17 : (prefix_suffix_sorted (app (l1_2) ((cons (key_2) (l2_2)))) l4_2 )) (PreH18 : (prefix_suffix_sorted l1_2 (cons (key_2) ((@nil Z))) )) ,
  TT && emp 
|--
  EX (l1: (@list Z))  (key: Z)  (l2: (@list Z))  (l4: (@list Z)) ,
  “ (l3_2 = (app ((app (l1) ((cons (key) (l2))))) (l4))) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l4))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (i < (numsSize_pre - 1 )) ” 
  &&  “ ((j + 1 ) = (Zlength (l1))) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ (((j + 1 ) + 1 ) <= (numsSize_pre - i )) ” 
  &&  “ ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ (Permutation l (app ((app (l1) ((cons (key) (l2))))) (l4)) ) ” 
  &&  “ (increasing l4 ) ” 
  &&  “ (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) ” 
  &&  “ (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) ) ”
  &&  emp
).

Definition sortArray_entail_wit_4 := 
(
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1_2: (@list Z)) (key: Z) (l2_2: (@list Z)) (l4: (@list Z)) (l3_2: (@list Z)) (PreH1 : ((j + 1 ) >= (numsSize_pre - i ))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3_2 = (app ((app (l1_2) ((cons (key) (l2_2))))) (l4)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l4)))) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (i < (numsSize_pre - 1 ))) (PreH10 : (j = (Zlength (l1_2)))) (PreH11 : (0 <= j)) (PreH12 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH13 : ((numsSize_pre - i ) = (Zlength ((app (l1_2) ((cons (key) (l2_2)))))))) (PreH14 : (Permutation l l3_2 )) (PreH15 : (increasing l4 )) (PreH16 : (prefix_suffix_sorted (app (l1_2) ((cons (key) (l2_2)))) l4 )) (PreH17 : (prefix_suffix_sorted l1_2 (cons (key) ((@nil Z))) )) ,
  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app (l1) (l2))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ ((i + 1 ) = (Zlength (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < numsSize_pre) ” 
  &&  “ (1 <= (Zlength (l1))) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l2 ) ” 
  &&  “ (prefix_suffix_sorted l1 l2 ) ”
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1_2: (@list Z)) (key: Z) (l2_2: (@list Z)) (l4: (@list Z)) (l3_2: (@list Z)) (PreH1 : ((j + 1 ) >= (numsSize_pre - i ))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3_2 = (app ((app (l1_2) ((cons (key) (l2_2))))) (l4)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l4)))) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (i < (numsSize_pre - 1 ))) (PreH10 : (j = (Zlength (l1_2)))) (PreH11 : (0 <= j)) (PreH12 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH13 : ((numsSize_pre - i ) = (Zlength ((app (l1_2) ((cons (key) (l2_2)))))))) (PreH14 : (Permutation l l3_2 )) (PreH15 : (increasing l4 )) (PreH16 : (prefix_suffix_sorted (app (l1_2) ((cons (key) (l2_2)))) l4 )) (PreH17 : (prefix_suffix_sorted l1_2 (cons (key) ((@nil Z))) )) ,
  TT && emp 
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l3_2 = (app (l1) (l2))) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ ((i + 1 ) = (Zlength (l2))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < numsSize_pre) ” 
  &&  “ (1 <= (Zlength (l1))) ” 
  &&  “ (Permutation l (app (l1) (l2)) ) ” 
  &&  “ (increasing l2 ) ” 
  &&  “ (prefix_suffix_sorted l1 l2 ) ”
  &&  emp
).

Definition sortArray_return_wit_1 := 
(
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (i: Z) (l1_2: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (i >= (numsSize_pre - 1 ))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (app (l1_2) (l2)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l2)))) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (1 <= (Zlength (l1_2)))) (PreH10 : (Permutation l l3 )) (PreH11 : (increasing l2 )) (PreH12 : (prefix_suffix_sorted l1_2 l2 )) ,
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
forall (numsSize_pre: Z) (l: (@list Z)) (i: Z) (l1_2: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (i >= (numsSize_pre - 1 ))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (app (l1_2) (l2)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l2)))) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (1 <= (Zlength (l1_2)))) (PreH10 : (Permutation l l3 )) (PreH11 : (increasing l2 )) (PreH12 : (prefix_suffix_sorted l1_2 l2 )) ,
  TT && emp 
|--
  “ ((Zlength (l3)) = numsSize_pre) ” 
  &&  “ (increasing l3 ) ”
  &&  emp
).

Definition sortArray_return_wit_1_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (i: Z) (l1_2: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (i >= (numsSize_pre - 1 ))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (app (l1_2) (l2)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l2)))) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (1 <= (Zlength (l1_2)))) (PreH10 : (Permutation l l3 )) (PreH11 : (increasing l2 )) (PreH12 : (prefix_suffix_sorted l1_2 l2 )) ,
  ((Zlength (l3)) = numsSize_pre)
.

Definition sortArray_return_wit_1_split_goal_2 := 
forall (numsSize_pre: Z) (l: (@list Z)) (i: Z) (l1_2: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (i >= (numsSize_pre - 1 ))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (app (l1_2) (l2)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l2)))) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (1 <= (Zlength (l1_2)))) (PreH10 : (Permutation l l3 )) (PreH11 : (increasing l2 )) (PreH12 : (prefix_suffix_sorted l1_2 l2 )) ,
  (increasing l3 )
.

Definition sortArray_return_wit_2 := 
(
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (numsSize_pre <= 1)) (PreH2 : ((Zlength (l)) = numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ ((Zlength (l1)) = numsSize_pre) ”
  &&  (IntArray.full nums_pre numsSize_pre l1 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (PreH1 : (numsSize_pre <= 1)) (PreH2 : ((Zlength (l)) = numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) ,
  TT && emp 
|--
  “ (increasing l ) ” 
  &&  “ (Permutation l l ) ”
  &&  emp
).

Definition sortArray_return_wit_2_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (PreH1 : (numsSize_pre <= 1)) (PreH2 : ((Zlength (l)) = numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) ,
  (increasing l )
.

Definition sortArray_return_wit_2_split_goal_2 := 
forall (numsSize_pre: Z) (l: (@list Z)) (PreH1 : (numsSize_pre <= 1)) (PreH2 : ((Zlength (l)) = numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) ,
  (Permutation l l )
.

Definition sortArray_partial_solve_wit_1 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((j + 1 ) < (numsSize_pre - i ))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l4)))) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (i < (numsSize_pre - 1 ))) (PreH10 : (j = (Zlength (l1)))) (PreH11 : (0 <= j)) (PreH12 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH13 : ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH14 : (Permutation l l3 )) (PreH15 : (increasing l4 )) (PreH16 : (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 )) (PreH17 : (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) )) ,
  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.full nums_pre numsSize_pre l3 )
|--
  “ ((j + 1 ) < (numsSize_pre - i )) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l4))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (i < (numsSize_pre - 1 )) ” 
  &&  “ (j = (Zlength (l1))) ” 
  &&  “ (0 <= j) ” 
  &&  “ ((j + 1 ) <= (numsSize_pre - i )) ” 
  &&  “ ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l4 ) ” 
  &&  “ (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) ” 
  &&  “ (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) ) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int  |-> (Znth j l3 0))
  **  (IntArray.missing_i nums_pre j 0 numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Definition sortArray_partial_solve_wit_2 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((j + 1 ) < (numsSize_pre - i ))) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4)))) (PreH5 : (numsSize_pre = (Zlength (l)))) (PreH6 : (i = (Zlength (l4)))) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (i < (numsSize_pre - 1 ))) (PreH10 : (j = (Zlength (l1)))) (PreH11 : (0 <= j)) (PreH12 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH13 : ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH14 : (Permutation l l3 )) (PreH15 : (increasing l4 )) (PreH16 : (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 )) (PreH17 : (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) )) ,
  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  “ ((j + 1 ) < (numsSize_pre - i )) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l4))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (i < (numsSize_pre - 1 )) ” 
  &&  “ (j = (Zlength (l1))) ” 
  &&  “ (0 <= j) ” 
  &&  “ ((j + 1 ) <= (numsSize_pre - i )) ” 
  &&  “ ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l4 ) ” 
  &&  “ (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) ” 
  &&  “ (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) ) ”
  &&  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth (j + 1 ) l3 0))
  **  (IntArray.missing_i nums_pre (j + 1 ) 0 numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Definition sortArray_partial_solve_wit_3 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth j l3 0) > (Znth (j + 1 ) l3 0))) (PreH2 : ((j + 1 ) < (numsSize_pre - i ))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1 ))) (PreH11 : (j = (Zlength (l1)))) (PreH12 : (0 <= j)) (PreH13 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH14 : ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH15 : (Permutation l l3 )) (PreH16 : (increasing l4 )) (PreH17 : (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 )) (PreH18 : (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) )) ,
  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  “ ((Znth j l3 0) > (Znth (j + 1 ) l3 0)) ” 
  &&  “ ((j + 1 ) < (numsSize_pre - i )) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l4))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (i < (numsSize_pre - 1 )) ” 
  &&  “ (j = (Zlength (l1))) ” 
  &&  “ (0 <= j) ” 
  &&  “ ((j + 1 ) <= (numsSize_pre - i )) ” 
  &&  “ ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l4 ) ” 
  &&  “ (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) ” 
  &&  “ (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) ) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int  |-> (Znth j l3 0))
  **  (IntArray.missing_i nums_pre j 0 numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Definition sortArray_partial_solve_wit_4 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth j l3 0) > (Znth (j + 1 ) l3 0))) (PreH2 : ((j + 1 ) < (numsSize_pre - i ))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1 ))) (PreH11 : (j = (Zlength (l1)))) (PreH12 : (0 <= j)) (PreH13 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH14 : ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH15 : (Permutation l l3 )) (PreH16 : (increasing l4 )) (PreH17 : (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 )) (PreH18 : (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) )) ,
  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  “ ((Znth j l3 0) > (Znth (j + 1 ) l3 0)) ” 
  &&  “ ((j + 1 ) < (numsSize_pre - i )) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l4))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (i < (numsSize_pre - 1 )) ” 
  &&  “ (j = (Zlength (l1))) ” 
  &&  “ (0 <= j) ” 
  &&  “ ((j + 1 ) <= (numsSize_pre - i )) ” 
  &&  “ ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l4 ) ” 
  &&  “ (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) ” 
  &&  “ (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) ) ”
  &&  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth (j + 1 ) l3 0))
  **  (IntArray.missing_i nums_pre (j + 1 ) 0 numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Definition sortArray_partial_solve_wit_5 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth j l3 0) > (Znth (j + 1 ) l3 0))) (PreH2 : ((j + 1 ) < (numsSize_pre - i ))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1 ))) (PreH11 : (j = (Zlength (l1)))) (PreH12 : (0 <= j)) (PreH13 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH14 : ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH15 : (Permutation l l3 )) (PreH16 : (increasing l4 )) (PreH17 : (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 )) (PreH18 : (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) )) ,
  (IntArray.full nums_pre numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  “ ((Znth j l3 0) > (Znth (j + 1 ) l3 0)) ” 
  &&  “ ((j + 1 ) < (numsSize_pre - i )) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l4))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (i < (numsSize_pre - 1 )) ” 
  &&  “ (j = (Zlength (l1))) ” 
  &&  “ (0 <= j) ” 
  &&  “ ((j + 1 ) <= (numsSize_pre - i )) ” 
  &&  “ ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l4 ) ” 
  &&  “ (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) ” 
  &&  “ (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) ) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre j 0 numsSize_pre l3 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Definition sortArray_partial_solve_wit_6 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (i: Z) (l1: (@list Z)) (key: Z) (l2: (@list Z)) (l4: (@list Z)) (l3: (@list Z)) (PreH1 : ((Znth j l3 0) > (Znth (j + 1 ) l3 0))) (PreH2 : ((j + 1 ) < (numsSize_pre - i ))) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4)))) (PreH6 : (numsSize_pre = (Zlength (l)))) (PreH7 : (i = (Zlength (l4)))) (PreH8 : (0 <= i)) (PreH9 : (i < numsSize_pre)) (PreH10 : (i < (numsSize_pre - 1 ))) (PreH11 : (j = (Zlength (l1)))) (PreH12 : (0 <= j)) (PreH13 : ((j + 1 ) <= (numsSize_pre - i ))) (PreH14 : ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2)))))))) (PreH15 : (Permutation l l3 )) (PreH16 : (increasing l4 )) (PreH17 : (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 )) (PreH18 : (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) )) ,
  (IntArray.full nums_pre numsSize_pre (replace_Znth (j) ((Znth (j + 1 ) l3 0)) (l3)) )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
|--
  “ ((Znth j l3 0) > (Znth (j + 1 ) l3 0)) ” 
  &&  “ ((j + 1 ) < (numsSize_pre - i )) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l3 = (app ((app (l1) ((cons (key) (l2))))) (l4))) ” 
  &&  “ (numsSize_pre = (Zlength (l))) ” 
  &&  “ (i = (Zlength (l4))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (i < (numsSize_pre - 1 )) ” 
  &&  “ (j = (Zlength (l1))) ” 
  &&  “ (0 <= j) ” 
  &&  “ ((j + 1 ) <= (numsSize_pre - i )) ” 
  &&  “ ((numsSize_pre - i ) = (Zlength ((app (l1) ((cons (key) (l2))))))) ” 
  &&  “ (Permutation l l3 ) ” 
  &&  “ (increasing l4 ) ” 
  &&  “ (prefix_suffix_sorted (app (l1) ((cons (key) (l2)))) l4 ) ” 
  &&  “ (prefix_suffix_sorted l1 (cons (key) ((@nil Z))) ) ”
  &&  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) 0 numsSize_pre (replace_Znth (j) ((Znth (j + 1 ) l3 0)) (l3)) )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
.

Module Type VC_Correct.


Axiom proof_of_sortArray_safety_wit_1 : sortArray_safety_wit_1.
Axiom proof_of_sortArray_safety_wit_2 : sortArray_safety_wit_2.
Axiom proof_of_sortArray_safety_wit_3 : sortArray_safety_wit_3.
Axiom proof_of_sortArray_safety_wit_4 : sortArray_safety_wit_4.
Axiom proof_of_sortArray_safety_wit_5 : sortArray_safety_wit_5.
Axiom proof_of_sortArray_safety_wit_6 : sortArray_safety_wit_6.
Axiom proof_of_sortArray_safety_wit_7 : sortArray_safety_wit_7.
Axiom proof_of_sortArray_safety_wit_8 : sortArray_safety_wit_8.
Axiom proof_of_sortArray_safety_wit_9 : sortArray_safety_wit_9.
Axiom proof_of_sortArray_safety_wit_10 : sortArray_safety_wit_10.
Axiom proof_of_sortArray_safety_wit_11 : sortArray_safety_wit_11.
Axiom proof_of_sortArray_safety_wit_12 : sortArray_safety_wit_12.
Axiom proof_of_sortArray_safety_wit_13 : sortArray_safety_wit_13.
Axiom proof_of_sortArray_safety_wit_14 : sortArray_safety_wit_14.
Axiom proof_of_sortArray_safety_wit_15 : sortArray_safety_wit_15.
Axiom proof_of_sortArray_safety_wit_16 : sortArray_safety_wit_16.
Axiom proof_of_sortArray_safety_wit_17 : sortArray_safety_wit_17.
Axiom proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1.
Axiom proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2.
Axiom proof_of_sortArray_entail_wit_3_1 : sortArray_entail_wit_3_1.
Axiom proof_of_sortArray_entail_wit_3_2 : sortArray_entail_wit_3_2.
Axiom proof_of_sortArray_entail_wit_4 : sortArray_entail_wit_4.
Axiom proof_of_sortArray_return_wit_1 : sortArray_return_wit_1.
Axiom proof_of_sortArray_return_wit_2 : sortArray_return_wit_2.
Axiom proof_of_sortArray_partial_solve_wit_1 : sortArray_partial_solve_wit_1.
Axiom proof_of_sortArray_partial_solve_wit_2 : sortArray_partial_solve_wit_2.
Axiom proof_of_sortArray_partial_solve_wit_3 : sortArray_partial_solve_wit_3.
Axiom proof_of_sortArray_partial_solve_wit_4 : sortArray_partial_solve_wit_4.
Axiom proof_of_sortArray_partial_solve_wit_5 : sortArray_partial_solve_wit_5.
Axiom proof_of_sortArray_partial_solve_wit_6 : sortArray_partial_solve_wit_6.

End VC_Correct.
