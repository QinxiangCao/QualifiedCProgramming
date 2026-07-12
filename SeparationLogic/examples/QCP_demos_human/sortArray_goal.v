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
Require Import SimpleC.EE.QCP_demos_human.sortArray_lib.
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
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sortArray_safety_wit_2 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (app (l1) (l2)))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : (1 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (Permutation l1 l0 )) (PreH9 : (increasing l0 )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.seg nums_pre i numsSize_pre l2 )
  **  ((( &( "key" ) )) # Int  |-> (Znth (i - i ) l2 0))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 i l0 )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition sortArray_safety_wit_3 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (app (l1) (l2)))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : (1 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (Permutation l1 l0 )) (PreH9 : (increasing l0 )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.seg nums_pre i numsSize_pre l2 )
  **  ((( &( "key" ) )) # Int  |-> (Znth (i - i ) l2 0))
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 i l0 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sortArray_safety_wit_4 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2: (@list Z)) (l3: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (key: Z) (l4: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 50000)) (PreH3 : (l = (app (l1) ((cons (key) (l4)))))) (PreH4 : (i = (Zlength (l1)))) (PreH5 : (1 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (Permutation l1 l0 )) (PreH8 : (increasing l0 )) (PreH9 : (l0 = (app (l2) (l3)))) (PreH10 : ((j + 1 ) = (Zlength (l2)))) (PreH11 : ((j + 1 ) <= i)) (PreH12 : (strict_lowerbound key l3 )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 (j + 1 ) l2 )
  **  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sortArray_safety_wit_5 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (l0: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (l5: (@list Z)) (j: Z) (i: Z) (key: Z) (PreH1 : (l2 = (app (l5) ((cons ((Znth j l2 0)) ((@nil Z))))))) (PreH2 : (j = (Zlength (l5)))) (PreH3 : ((j + 1 ) <= i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 50000)) (PreH6 : (l = (app (l1) ((cons (key) (l4)))))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (1 <= i)) (PreH9 : (i <= numsSize_pre)) (PreH10 : (Permutation l1 l0 )) (PreH11 : (increasing l0 )) (PreH12 : (l0 = (app (l2) (l3)))) (PreH13 : (strict_lowerbound key l3 )) (PreH14 : (0 <= j)) (PreH15 : ((Znth j l2 0) > key)) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 j l5 )
  **  (((nums_pre + (j * sizeof(INT)))) # Int  |-> (Znth j l2 0))
  **  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sortArray_safety_wit_6 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (l0: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (l5: (@list Z)) (j: Z) (i: Z) (key: Z) (PreH1 : (l2 = (app (l5) ((cons ((Znth j l2 0)) ((@nil Z))))))) (PreH2 : (j = (Zlength (l5)))) (PreH3 : ((j + 1 ) <= i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 50000)) (PreH6 : (l = (app (l1) ((cons (key) (l4)))))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (1 <= i)) (PreH9 : (i <= numsSize_pre)) (PreH10 : (Permutation l1 l0 )) (PreH11 : (increasing l0 )) (PreH12 : (l0 = (app (l2) (l3)))) (PreH13 : (strict_lowerbound key l3 )) (PreH14 : (0 <= j)) (PreH15 : ((Znth j l2 0) > key)) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 j l5 )
  **  (((nums_pre + (j * sizeof(INT)))) # Int  |-> (Znth j l2 0))
  **  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sortArray_safety_wit_7 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (l0: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (l5: (@list Z)) (j: Z) (i: Z) (key: Z) (PreH1 : (l2 = (app (l5) ((cons ((Znth j l2 0)) ((@nil Z))))))) (PreH2 : (j = (Zlength (l5)))) (PreH3 : ((j + 1 ) <= i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 50000)) (PreH6 : (l = (app (l1) ((cons (key) (l4)))))) (PreH7 : (i = (Zlength (l1)))) (PreH8 : (1 <= i)) (PreH9 : (i <= numsSize_pre)) (PreH10 : (Permutation l1 l0 )) (PreH11 : (increasing l0 )) (PreH12 : (l0 = (app (l2) (l3)))) (PreH13 : (strict_lowerbound key l3 )) (PreH14 : (0 <= j)) (PreH15 : ((Znth j l2 0) > key)) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 j l5 )
  **  (((nums_pre + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre j j (i + 1 ) (cons (key) ((cons ((Znth j l2 0)) (l3)))) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition sortArray_safety_wit_8 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2: (@list Z)) (l3: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (key: Z) (l4: (@list Z)) (PreH1 : ((Znth (j - 0 ) l2 0) <= key)) (PreH2 : (j >= 0)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l = (app (l1) ((cons (key) (l4)))))) (PreH6 : (i = (Zlength (l1)))) (PreH7 : (1 <= i)) (PreH8 : (i <= numsSize_pre)) (PreH9 : (Permutation l1 l0 )) (PreH10 : (increasing l0 )) (PreH11 : (l0 = (app (l2) (l3)))) (PreH12 : ((j + 1 ) = (Zlength (l2)))) (PreH13 : ((j + 1 ) <= i)) (PreH14 : (strict_lowerbound key l3 )) ,
  (IntArray.seg nums_pre 0 (j + 1 ) l2 )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sortArray_safety_wit_9 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2: (@list Z)) (l3: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (key: Z) (l4: (@list Z)) (PreH1 : (j < 0)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (app (l1) ((cons (key) (l4)))))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : (1 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (Permutation l1 l0 )) (PreH9 : (increasing l0 )) (PreH10 : (l0 = (app (l2) (l3)))) (PreH11 : ((j + 1 ) = (Zlength (l2)))) (PreH12 : ((j + 1 ) <= i)) (PreH13 : (strict_lowerbound key l3 )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 (j + 1 ) l2 )
  **  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sortArray_safety_wit_10 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2: (@list Z)) (l3: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (key: Z) (l4: (@list Z)) (PreH1 : (j < 0)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (app (l1) ((cons (key) (l4)))))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : (1 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (Permutation l1 l0 )) (PreH9 : (increasing l0 )) (PreH10 : (l0 = (app (l2) (l3)))) (PreH11 : ((j + 1 ) = (Zlength (l2)))) (PreH12 : ((j + 1 ) <= i)) (PreH13 : (strict_lowerbound key l3 )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 (j + 1 ) l2 )
  **  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sortArray_safety_wit_11 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2: (@list Z)) (l3: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (key: Z) (l4: (@list Z)) (PreH1 : ((Znth (j - 0 ) l2 0) <= key)) (PreH2 : (j >= 0)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l = (app (l1) ((cons (key) (l4)))))) (PreH6 : (i = (Zlength (l1)))) (PreH7 : (1 <= i)) (PreH8 : (i <= numsSize_pre)) (PreH9 : (Permutation l1 l0 )) (PreH10 : (increasing l0 )) (PreH11 : (l0 = (app (l2) (l3)))) (PreH12 : ((j + 1 ) = (Zlength (l2)))) (PreH13 : ((j + 1 ) <= i)) (PreH14 : (strict_lowerbound key l3 )) ,
  (IntArray.seg nums_pre 0 (j + 1 ) l2 )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "key" ) )) # Int  |-> key)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sortArray_safety_wit_12 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2: (@list Z)) (l3: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (key: Z) (l4: (@list Z)) (PreH1 : (j < 0)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (app (l1) ((cons (key) (l4)))))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : (1 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (Permutation l1 l0 )) (PreH9 : (increasing l0 )) (PreH10 : (l0 = (app (l2) (l3)))) (PreH11 : ((j + 1 ) = (Zlength (l2)))) (PreH12 : ((j + 1 ) <= i)) (PreH13 : (strict_lowerbound key l3 )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 (j + 1 ) l2 )
  **  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |-> key)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sortArray_safety_wit_13 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2: (@list Z)) (l3: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (key: Z) (l4: (@list Z)) (PreH1 : ((Znth (j - 0 ) l2 0) <= key)) (PreH2 : (j >= 0)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l = (app (l1) ((cons (key) (l4)))))) (PreH6 : (i = (Zlength (l1)))) (PreH7 : (1 <= i)) (PreH8 : (i <= numsSize_pre)) (PreH9 : (Permutation l1 l0 )) (PreH10 : (increasing l0 )) (PreH11 : (l0 = (app (l2) (l3)))) (PreH12 : ((j + 1 ) = (Zlength (l2)))) (PreH13 : ((j + 1 ) <= i)) (PreH14 : (strict_lowerbound key l3 )) ,
  (IntArray.seg nums_pre 0 (j + 1 ) l2 )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "returnSize" ) )) # Ptr  |-> returnSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |-> key)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
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
  EX (l0: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (1 = (Zlength (l1))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (Permutation l1 l0 ) ” 
  &&  “ (increasing l0 ) ”
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 1 l0 )
  **  (IntArray.seg nums_pre 1 numsSize_pre l2 )
) \/
(
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) ,
  (IntArray.full nums_pre numsSize_pre l )
|--
  EX (l0: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (1 = (Zlength (l1))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (Permutation l1 l0 ) ” 
  &&  “ (increasing l0 ) ”
  &&  (IntArray.seg nums_pre 0 1 l0 )
  **  (IntArray.seg nums_pre 1 numsSize_pre l2 )
).

Definition sortArray_entail_wit_2 := 
(
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l0_2: (@list Z)) (i: Z) (l1_2: (@list Z)) (l2: (@list Z)) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (app (l1_2) (l2)))) (PreH5 : (i = (Zlength (l1_2)))) (PreH6 : (1 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (Permutation l1_2 l0_2 )) (PreH9 : (increasing l0_2 )) ,
  (IntArray.seg nums_pre i numsSize_pre l2 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 i l0_2 )
|--
  EX (l2_2: (@list Z))  (l3: (@list Z))  (l0: (@list Z))  (l1: (@list Z))  (l4: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l = (app (l1) ((cons ((Znth (i - i ) l2 0)) (l4))))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (Permutation l1 l0 ) ” 
  &&  “ (increasing l0 ) ” 
  &&  “ (l0 = (app (l2_2) (l3))) ” 
  &&  “ (((i - 1 ) + 1 ) = (Zlength (l2_2))) ” 
  &&  “ (((i - 1 ) + 1 ) <= i) ” 
  &&  “ (strict_lowerbound (Znth (i - i ) l2 0) l3 ) ”
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 ((i - 1 ) + 1 ) l2_2 )
  **  (((nums_pre + (((i - 1 ) + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre ((i - 1 ) + 1 ) ((i - 1 ) + 1 ) (i + 1 ) (cons ((Znth (i - i ) l2 0)) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
) \/
(
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l0_2: (@list Z)) (i: Z) (l1_2: (@list Z)) (l2: (@list Z)) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (app (l1_2) (l2)))) (PreH5 : (i = (Zlength (l1_2)))) (PreH6 : (1 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (Permutation l1_2 l0_2 )) (PreH9 : (increasing l0_2 )) ,
  (IntArray.missing_i nums_pre ((i - 1 ) + 1 ) i numsSize_pre l2 )
  **  (IntArray.seg nums_pre 0 i l0_2 )
|--
  EX (l2_2: (@list Z))  (l3: (@list Z))  (l1: (@list Z))  (l4: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l = (app (l1) ((cons ((Znth (i - i ) l2 0)) (l4))))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (Permutation l1 (app (l2_2) (l3)) ) ” 
  &&  “ (increasing (app (l2_2) (l3)) ) ” 
  &&  “ (((i - 1 ) + 1 ) = (Zlength (l2_2))) ” 
  &&  “ (((i - 1 ) + 1 ) <= i) ” 
  &&  “ (strict_lowerbound (Znth (i - i ) l2 0) l3 ) ”
  &&  (IntArray.seg nums_pre 0 ((i - 1 ) + 1 ) l2_2 )
  **  (IntArray.missing_i nums_pre ((i - 1 ) + 1 ) ((i - 1 ) + 1 ) (i + 1 ) (cons ((Znth (i - i ) l2 0)) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
).

Definition sortArray_entail_wit_3 := 
(
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2_2: (@list Z)) (l3_2: (@list Z)) (l0_2: (@list Z)) (i: Z) (l1_2: (@list Z)) (key: Z) (l4_2: (@list Z)) (PreH1 : ((Znth (j - 0 ) l2_2 0) > key)) (PreH2 : (j >= 0)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l = (app (l1_2) ((cons (key) (l4_2)))))) (PreH6 : (i = (Zlength (l1_2)))) (PreH7 : (1 <= i)) (PreH8 : (i <= numsSize_pre)) (PreH9 : (Permutation l1_2 l0_2 )) (PreH10 : (increasing l0_2 )) (PreH11 : (l0_2 = (app (l2_2) (l3_2)))) (PreH12 : ((j + 1 ) = (Zlength (l2_2)))) (PreH13 : ((j + 1 ) <= i)) (PreH14 : (strict_lowerbound key l3_2 )) ,
  (IntArray.seg nums_pre 0 (j + 1 ) l2_2 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3_2)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4_2 )
|--
  EX (l3: (@list Z))  (l0: (@list Z))  (l1: (@list Z))  (l4: (@list Z))  (l5: (@list Z))  (l2: (@list Z)) ,
  “ (l2 = (app (l5) ((cons ((Znth j l2 0)) ((@nil Z)))))) ” 
  &&  “ (j = (Zlength (l5))) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l = (app (l1) ((cons (key) (l4))))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (Permutation l1 l0 ) ” 
  &&  “ (increasing l0 ) ” 
  &&  “ (l0 = (app (l2) (l3))) ” 
  &&  “ (strict_lowerbound key l3 ) ” 
  &&  “ (0 <= j) ” 
  &&  “ ((Znth j l2 0) > key) ”
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 j l5 )
  **  (((nums_pre + (j * sizeof(INT)))) # Int  |-> (Znth j l2 0))
  **  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
) \/
(
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2_2: (@list Z)) (l3_2: (@list Z)) (l0_2: (@list Z)) (i: Z) (l1_2: (@list Z)) (key: Z) (l4_2: (@list Z)) (l2: (@list Z)) (PreH1 : ((Znth (j - 0 ) l2_2 0) > key)) (PreH2 : (j >= 0)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l = (app (l1_2) ((cons (key) (l4_2)))))) (PreH6 : (i = (Zlength (l1_2)))) (PreH7 : (1 <= i)) (PreH8 : (i <= numsSize_pre)) (PreH9 : (Permutation l1_2 l0_2 )) (PreH10 : (increasing l0_2 )) (PreH11 : (l0_2 = (app (l2_2) (l3_2)))) (PreH12 : ((j + 1 ) = (Zlength (l2_2)))) (PreH13 : ((j + 1 ) <= i)) (PreH14 : (strict_lowerbound key l3_2 )) ,
  (IntArray.missing_i nums_pre j 0 (j + 1 ) l2_2 )
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3_2)) )
|--
  EX (l3: (@list Z))  (l1: (@list Z))  (l5: (@list Z)) ,
  “ ((Znth j (app (l5) ((cons ((Znth j l2 0)) ((@nil Z))))) 0) = (Znth (j - 0 ) l2_2 0)) ” 
  &&  “ ((app (l5) ((cons ((Znth j l2 0)) ((@nil Z))))) = (app (l5) ((cons ((Znth j (app (l5) ((cons ((Znth j l2 0)) ((@nil Z))))) 0)) ((@nil Z)))))) ” 
  &&  “ (j = (Zlength (l5))) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l = (app (l1) ((cons (key) (l4_2))))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (Permutation l1 (app ((app (l5) ((cons ((Znth j l2 0)) ((@nil Z)))))) (l3)) ) ” 
  &&  “ (increasing (app ((app (l5) ((cons ((Znth j l2 0)) ((@nil Z)))))) (l3)) ) ” 
  &&  “ (strict_lowerbound key l3 ) ” 
  &&  “ (0 <= j) ” 
  &&  “ ((Znth j (app (l5) ((cons ((Znth j l2 0)) ((@nil Z))))) 0) > key) ”
  &&  (IntArray.seg nums_pre 0 j l5 )
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
).

Definition sortArray_entail_wit_4 := 
(
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l0_2: (@list Z)) (l3_2: (@list Z)) (l4_2: (@list Z)) (l5_2: (@list Z)) (j: Z) (i: Z) (key: Z) (PreH1 : (l2_2 = (app (l5_2) ((cons ((Znth j l2_2 0)) ((@nil Z))))))) (PreH2 : (j = (Zlength (l5_2)))) (PreH3 : ((j + 1 ) <= i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 50000)) (PreH6 : (l = (app (l1_2) ((cons (key) (l4_2)))))) (PreH7 : (i = (Zlength (l1_2)))) (PreH8 : (1 <= i)) (PreH9 : (i <= numsSize_pre)) (PreH10 : (Permutation l1_2 l0_2 )) (PreH11 : (increasing l0_2 )) (PreH12 : (l0_2 = (app (l2_2) (l3_2)))) (PreH13 : (strict_lowerbound key l3_2 )) (PreH14 : (0 <= j)) (PreH15 : ((Znth j l2_2 0) > key)) ,
  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 j l5_2 )
  **  (((nums_pre + (j * sizeof(INT)))) # Int  |-> (Znth j l2_2 0))
  **  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth j l2_2 0))
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3_2)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4_2 )
|--
  EX (l3: (@list Z))  (l0: (@list Z))  (l1: (@list Z))  (l4: (@list Z))  (l5: (@list Z))  (l2: (@list Z)) ,
  “ (l2 = (app (l5) ((cons ((Znth j l2 0)) ((@nil Z)))))) ” 
  &&  “ (j = (Zlength (l5))) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l = (app (l1) ((cons (key) (l4))))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (Permutation l1 l0 ) ” 
  &&  “ (increasing l0 ) ” 
  &&  “ (l0 = (app (l2) (l3))) ” 
  &&  “ (strict_lowerbound key l3 ) ” 
  &&  “ (0 <= j) ” 
  &&  “ ((Znth j l2 0) > key) ”
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 j l5 )
  **  (((nums_pre + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre j j (i + 1 ) (cons (key) ((cons ((Znth j l2 0)) (l3)))) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
) \/
(
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l0_2: (@list Z)) (l3_2: (@list Z)) (l4_2: (@list Z)) (l5_2: (@list Z)) (j: Z) (i: Z) (key: Z) (l2: (@list Z)) (PreH1 : ((Znth j l2_2 0) <= INT_MAX)) (PreH2 : ((Znth j l2_2 0) >= INT_MIN)) (PreH3 : (l2_2 = (app (l5_2) ((cons ((Znth j l2_2 0)) ((@nil Z))))))) (PreH4 : (j = (Zlength (l5_2)))) (PreH5 : ((j + 1 ) <= i)) (PreH6 : (1 <= numsSize_pre)) (PreH7 : (numsSize_pre <= 50000)) (PreH8 : (l = (app (l1_2) ((cons (key) (l4_2)))))) (PreH9 : (i = (Zlength (l1_2)))) (PreH10 : (1 <= i)) (PreH11 : (i <= numsSize_pre)) (PreH12 : (Permutation l1_2 l0_2 )) (PreH13 : (increasing l0_2 )) (PreH14 : (l0_2 = (app (l2_2) (l3_2)))) (PreH15 : (strict_lowerbound key l3_2 )) (PreH16 : (0 <= j)) (PreH17 : ((Znth j l2_2 0) > key)) ,
  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth j l2_2 0))
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3_2)) )
|--
  EX (l3: (@list Z))  (l1: (@list Z)) ,
  “ ((app (l5_2) ((cons ((Znth j l2 0)) ((@nil Z))))) = (app (l5_2) ((cons ((Znth j (app (l5_2) ((cons ((Znth j l2 0)) ((@nil Z))))) 0)) ((@nil Z)))))) ” 
  &&  “ (j = (Zlength (l5_2))) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l = (app (l1) ((cons (key) (l4_2))))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (Permutation l1 (app ((app (l5_2) ((cons ((Znth j l2 0)) ((@nil Z)))))) (l3)) ) ” 
  &&  “ (increasing (app ((app (l5_2) ((cons ((Znth j l2 0)) ((@nil Z)))))) (l3)) ) ” 
  &&  “ (strict_lowerbound key l3 ) ” 
  &&  “ (0 <= j) ” 
  &&  “ ((Znth j (app (l5_2) ((cons ((Znth j l2 0)) ((@nil Z))))) 0) > key) ”
  &&  (IntArray.missing_i nums_pre j j (i + 1 ) (cons (key) ((cons ((Znth j (app (l5_2) ((cons ((Znth j l2 0)) ((@nil Z))))) 0)) (l3)))) )
).

Definition sortArray_entail_wit_5 := 
(
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l0_2: (@list Z)) (l3_2: (@list Z)) (l4_2: (@list Z)) (l5: (@list Z)) (j: Z) (i: Z) (key: Z) (PreH1 : (l2_2 = (app (l5) ((cons ((Znth j l2_2 0)) ((@nil Z))))))) (PreH2 : (j = (Zlength (l5)))) (PreH3 : ((j + 1 ) <= i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 50000)) (PreH6 : (l = (app (l1_2) ((cons (key) (l4_2)))))) (PreH7 : (i = (Zlength (l1_2)))) (PreH8 : (1 <= i)) (PreH9 : (i <= numsSize_pre)) (PreH10 : (Permutation l1_2 l0_2 )) (PreH11 : (increasing l0_2 )) (PreH12 : (l0_2 = (app (l2_2) (l3_2)))) (PreH13 : (strict_lowerbound key l3_2 )) (PreH14 : (0 <= j)) (PreH15 : ((Znth j l2_2 0) > key)) ,
  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 j l5 )
  **  (((nums_pre + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre j j (i + 1 ) (cons (key) ((cons ((Znth j l2_2 0)) (l3_2)))) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4_2 )
|--
  EX (l2: (@list Z))  (l3: (@list Z))  (l0: (@list Z))  (l1: (@list Z))  (l4: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l = (app (l1) ((cons (key) (l4))))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (Permutation l1 l0 ) ” 
  &&  “ (increasing l0 ) ” 
  &&  “ (l0 = (app (l2) (l3))) ” 
  &&  “ (((j - 1 ) + 1 ) = (Zlength (l2))) ” 
  &&  “ (((j - 1 ) + 1 ) <= i) ” 
  &&  “ (strict_lowerbound key l3 ) ”
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 ((j - 1 ) + 1 ) l2 )
  **  (((nums_pre + (((j - 1 ) + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre ((j - 1 ) + 1 ) ((j - 1 ) + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
) \/
(
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l0_2: (@list Z)) (l3_2: (@list Z)) (l4_2: (@list Z)) (l5: (@list Z)) (j: Z) (i: Z) (key: Z) (PreH1 : (l2_2 = (app (l5) ((cons ((Znth j l2_2 0)) ((@nil Z))))))) (PreH2 : (j = (Zlength (l5)))) (PreH3 : ((j + 1 ) <= i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 50000)) (PreH6 : (l = (app (l1_2) ((cons (key) (l4_2)))))) (PreH7 : (i = (Zlength (l1_2)))) (PreH8 : (1 <= i)) (PreH9 : (i <= numsSize_pre)) (PreH10 : (Permutation l1_2 l0_2 )) (PreH11 : (increasing l0_2 )) (PreH12 : (l0_2 = (app (l2_2) (l3_2)))) (PreH13 : (strict_lowerbound key l3_2 )) (PreH14 : (0 <= j)) (PreH15 : ((Znth j l2_2 0) > key)) ,
  (IntArray.seg nums_pre 0 j l5 )
  **  (((nums_pre + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre j j (i + 1 ) (cons (key) ((cons ((Znth j l2_2 0)) (l3_2)))) )
|--
  EX (x: Z)  (l2: (@list Z))  (l3: (@list Z))  (l1: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l = (app (l1) ((cons (key) (l4_2))))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (Permutation l1 (app (l2) (l3)) ) ” 
  &&  “ (increasing (app (l2) (l3)) ) ” 
  &&  “ (((j - 1 ) + 1 ) = (Zlength (l2))) ” 
  &&  “ (((j - 1 ) + 1 ) <= i) ” 
  &&  “ (strict_lowerbound key l3 ) ”
  &&  (((nums_pre + (((j - 1 ) + 1 ) * sizeof(INT)))) # Int  |-> x)
  **  (IntArray.seg nums_pre 0 ((j - 1 ) + 1 ) l2 )
  **  (IntArray.missing_i nums_pre ((j - 1 ) + 1 ) ((j - 1 ) + 1 ) (i + 1 ) (cons (key) (l3)) )
).

Definition sortArray_entail_wit_6_1 := 
(
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2_2: (@list Z)) (l3: (@list Z)) (l0_2: (@list Z)) (i: Z) (l1_2: (@list Z)) (key: Z) (l4: (@list Z)) (PreH1 : (j < 0)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (app (l1_2) ((cons (key) (l4)))))) (PreH5 : (i = (Zlength (l1_2)))) (PreH6 : (1 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (Permutation l1_2 l0_2 )) (PreH9 : (increasing l0_2 )) (PreH10 : (l0_2 = (app (l2_2) (l3)))) (PreH11 : ((j + 1 ) = (Zlength (l2_2)))) (PreH12 : ((j + 1 ) <= i)) (PreH13 : (strict_lowerbound key l3 )) ,
  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 (j + 1 ) l2_2 )
  **  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |-> key)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  EX (l0: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ ((i + 1 ) = (Zlength (l1))) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (Permutation l1 l0 ) ” 
  &&  “ (increasing l0 ) ”
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 (i + 1 ) l0 )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l2 )
) \/
(
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2_2: (@list Z)) (l3: (@list Z)) (l0_2: (@list Z)) (i: Z) (l1_2: (@list Z)) (key: Z) (l4: (@list Z)) (PreH1 : (key <= INT_MAX)) (PreH2 : (key >= INT_MIN)) (PreH3 : (j < 0)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 50000)) (PreH6 : (l = (app (l1_2) ((cons (key) (l4)))))) (PreH7 : (i = (Zlength (l1_2)))) (PreH8 : (1 <= i)) (PreH9 : (i <= numsSize_pre)) (PreH10 : (Permutation l1_2 l0_2 )) (PreH11 : (increasing l0_2 )) (PreH12 : (l0_2 = (app (l2_2) (l3)))) (PreH13 : ((j + 1 ) = (Zlength (l2_2)))) (PreH14 : ((j + 1 ) <= i)) (PreH15 : (strict_lowerbound key l3 )) ,
  (IntArray.seg nums_pre 0 (j + 1 ) l2_2 )
  **  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |-> key)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
|--
  EX (l0: (@list Z))  (l1: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l = (app (l1) (l4))) ” 
  &&  “ ((i + 1 ) = (Zlength (l1))) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (Permutation l1 l0 ) ” 
  &&  “ (increasing l0 ) ”
  &&  (IntArray.seg nums_pre 0 (i + 1 ) l0 )
).

Definition sortArray_entail_wit_6_2 := 
(
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2_2: (@list Z)) (l3: (@list Z)) (l0_2: (@list Z)) (i: Z) (l1_2: (@list Z)) (key: Z) (l4: (@list Z)) (PreH1 : ((Znth (j - 0 ) l2_2 0) <= key)) (PreH2 : (j >= 0)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 50000)) (PreH5 : (l = (app (l1_2) ((cons (key) (l4)))))) (PreH6 : (i = (Zlength (l1_2)))) (PreH7 : (1 <= i)) (PreH8 : (i <= numsSize_pre)) (PreH9 : (Permutation l1_2 l0_2 )) (PreH10 : (increasing l0_2 )) (PreH11 : (l0_2 = (app (l2_2) (l3)))) (PreH12 : ((j + 1 ) = (Zlength (l2_2)))) (PreH13 : ((j + 1 ) <= i)) (PreH14 : (strict_lowerbound key l3 )) ,
  (IntArray.seg nums_pre 0 (j + 1 ) l2_2 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |-> key)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  EX (l0: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ ((i + 1 ) = (Zlength (l1))) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (Permutation l1 l0 ) ” 
  &&  “ (increasing l0 ) ”
  &&  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 (i + 1 ) l0 )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l2 )
) \/
(
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2_2: (@list Z)) (l3: (@list Z)) (l0_2: (@list Z)) (i: Z) (l1_2: (@list Z)) (key: Z) (l4: (@list Z)) (PreH1 : (key <= INT_MAX)) (PreH2 : (key >= INT_MIN)) (PreH3 : ((Znth (j - 0 ) l2_2 0) <= key)) (PreH4 : (j >= 0)) (PreH5 : (1 <= numsSize_pre)) (PreH6 : (numsSize_pre <= 50000)) (PreH7 : (l = (app (l1_2) ((cons (key) (l4)))))) (PreH8 : (i = (Zlength (l1_2)))) (PreH9 : (1 <= i)) (PreH10 : (i <= numsSize_pre)) (PreH11 : (Permutation l1_2 l0_2 )) (PreH12 : (increasing l0_2 )) (PreH13 : (l0_2 = (app (l2_2) (l3)))) (PreH14 : ((j + 1 ) = (Zlength (l2_2)))) (PreH15 : ((j + 1 ) <= i)) (PreH16 : (strict_lowerbound key l3 )) ,
  (IntArray.seg nums_pre 0 (j + 1 ) l2_2 )
  **  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |-> key)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
|--
  EX (l0: (@list Z))  (l1: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l = (app (l1) (l4))) ” 
  &&  “ ((i + 1 ) = (Zlength (l1))) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (Permutation l1 l0 ) ” 
  &&  “ (increasing l0 ) ”
  &&  (IntArray.seg nums_pre 0 (i + 1 ) l0 )
).

Definition sortArray_return_wit_1 := 
(
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l0: (@list Z)) (i: Z) (l1_2: (@list Z)) (l2: (@list Z)) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (app (l1_2) (l2)))) (PreH5 : (i = (Zlength (l1_2)))) (PreH6 : (1 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (Permutation l1_2 l0 )) (PreH9 : (increasing l0 )) ,
  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 i l0 )
  **  (IntArray.seg nums_pre i numsSize_pre l2 )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ ((Zlength (l1)) = numsSize_pre) ”
  &&  (IntArray.full nums_pre numsSize_pre l1 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
) \/
(
forall (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l0: (@list Z)) (i: Z) (l1_2: (@list Z)) (l2: (@list Z)) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (app (l1_2) (l2)))) (PreH5 : (i = (Zlength (l1_2)))) (PreH6 : (1 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (Permutation l1_2 l0 )) (PreH9 : (increasing l0 )) ,
  (IntArray.seg nums_pre 0 i l0 )
  **  (IntArray.seg nums_pre i numsSize_pre l2 )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ ((Zlength (l1)) = numsSize_pre) ”
  &&  (IntArray.full nums_pre numsSize_pre l1 )
).

Definition sortArray_partial_solve_wit_1 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (app (l1) (l2)))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : (1 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (Permutation l1 l0 )) (PreH9 : (increasing l0 )) ,
  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 i l0 )
  **  (IntArray.seg nums_pre i numsSize_pre l2 )
|--
  “ (i < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (Permutation l1 l0 ) ” 
  &&  “ (increasing l0 ) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i - i ) l2 0))
  **  (IntArray.missing_i nums_pre i i numsSize_pre l2 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 i l0 )
.

Definition sortArray_partial_solve_wit_2 := 
forall (returnSize_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (j: Z) (l2: (@list Z)) (l3: (@list Z)) (l0: (@list Z)) (i: Z) (l1: (@list Z)) (key: Z) (l4: (@list Z)) (PreH1 : (j >= 0)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 50000)) (PreH4 : (l = (app (l1) ((cons (key) (l4)))))) (PreH5 : (i = (Zlength (l1)))) (PreH6 : (1 <= i)) (PreH7 : (i <= numsSize_pre)) (PreH8 : (Permutation l1 l0 )) (PreH9 : (increasing l0 )) (PreH10 : (l0 = (app (l2) (l3)))) (PreH11 : ((j + 1 ) = (Zlength (l2)))) (PreH12 : ((j + 1 ) <= i)) (PreH13 : (strict_lowerbound key l3 )) ,
  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (IntArray.seg nums_pre 0 (j + 1 ) l2 )
  **  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
|--
  “ (j >= 0) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 50000) ” 
  &&  “ (l = (app (l1) ((cons (key) (l4))))) ” 
  &&  “ (i = (Zlength (l1))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (Permutation l1 l0 ) ” 
  &&  “ (increasing l0 ) ” 
  &&  “ (l0 = (app (l2) (l3))) ” 
  &&  “ ((j + 1 ) = (Zlength (l2))) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (strict_lowerbound key l3 ) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int  |-> (Znth (j - 0 ) l2 0))
  **  (IntArray.missing_i nums_pre j 0 (j + 1 ) l2 )
  **  ((returnSize_pre) # Int  |-> numsSize_pre)
  **  (((nums_pre + ((j + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i nums_pre (j + 1 ) (j + 1 ) (i + 1 ) (cons (key) (l3)) )
  **  (IntArray.seg nums_pre (i + 1 ) numsSize_pre l4 )
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
Axiom proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1.
Axiom proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2.
Axiom proof_of_sortArray_entail_wit_3 : sortArray_entail_wit_3.
Axiom proof_of_sortArray_entail_wit_4 : sortArray_entail_wit_4.
Axiom proof_of_sortArray_entail_wit_5 : sortArray_entail_wit_5.
Axiom proof_of_sortArray_entail_wit_6_1 : sortArray_entail_wit_6_1.
Axiom proof_of_sortArray_entail_wit_6_2 : sortArray_entail_wit_6_2.
Axiom proof_of_sortArray_return_wit_1 : sortArray_return_wit_1.
Axiom proof_of_sortArray_partial_solve_wit_1 : sortArray_partial_solve_wit_1.
Axiom proof_of_sortArray_partial_solve_wit_2 : sortArray_partial_solve_wit_2.

End VC_Correct.
