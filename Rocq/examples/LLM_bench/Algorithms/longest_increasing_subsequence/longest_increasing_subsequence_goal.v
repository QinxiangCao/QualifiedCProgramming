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
Require Import SimpleC.EE.LLM_bench.Algorithms.longest_increasing_subsequence.longest_increasing_subsequence_lib.
Local Open Scope sac.

(*----- Function lengthOfLIS -----*)

Definition lengthOfLIS_safety_wit_1 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = numsSize_pre)) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_full dp_pre numsSize_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lengthOfLIS_safety_wit_2 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = numsSize_pre)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |-> 1)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_full dp_pre numsSize_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lengthOfLIS_safety_wit_3 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= numsSize_pre)) (PreH9 : (LISDPTablePrefix l d i )) (PreH10 : (LISBestSoFar l i ans )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 i d )
  **  (IntArray.undef_seg dp_pre i numsSize_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lengthOfLIS_safety_wit_4 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= numsSize_pre)) (PreH9 : (LISDPTablePrefix l d i )) (PreH10 : (LISBestSoFar l i ans )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full nums_pre numsSize_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lengthOfLIS_safety_wit_5 := 
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) < (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= numsSize_pre)) (PreH12 : (LISBestSoFar l i ans )) (PreH13 : (LISInnerProgress l d i j )) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (((Znth (j - 0 ) d 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (j - 0 ) d 0) + 1 )) ”
) \/
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) < (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= numsSize_pre)) (PreH12 : (LISBestSoFar l i ans )) (PreH13 : (LISInnerProgress l d i j )) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (((Znth (j - 0 ) d 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (j - 0 ) d 0) + 1 )) ”
).

Definition lengthOfLIS_safety_wit_5_split_goal_1 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) < (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= numsSize_pre)) (PreH12 : (LISBestSoFar l i ans )) (PreH13 : (LISInnerProgress l d i j )) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (((Znth (j - 0 ) d 0) + 1 ) <= INT_MAX) ”
.

Definition lengthOfLIS_safety_wit_5_split_goal_2 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) < (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= numsSize_pre)) (PreH12 : (LISBestSoFar l i ans )) (PreH13 : (LISInnerProgress l d i j )) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((INT_MIN) <= ((Znth (j - 0 ) d 0) + 1 )) ”
.

Definition lengthOfLIS_safety_wit_6 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) < (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= numsSize_pre)) (PreH12 : (LISBestSoFar l i ans )) (PreH13 : (LISInnerProgress l d i j )) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lengthOfLIS_safety_wit_7 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (((Znth (j - 0 ) d 0) + 1 ) > (Znth (i - 0 ) d 0))) (PreH2 : ((Znth j l 0) < (Znth i l 0))) (PreH3 : (j < i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= i)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= numsSize_pre)) (PreH13 : (LISBestSoFar l i ans )) (PreH14 : (LISInnerProgress l d i j )) ,
  (IntArray.full dp_pre (i + 1 ) (replace_Znth (i) (((Znth (j - 0 ) d 0) + 1 )) (d)) )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition lengthOfLIS_safety_wit_8 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (((Znth (j - 0 ) d 0) + 1 ) <= (Znth (i - 0 ) d 0))) (PreH2 : ((Znth j l 0) < (Znth i l 0))) (PreH3 : (j < i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= i)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= numsSize_pre)) (PreH13 : (LISBestSoFar l i ans )) (PreH14 : (LISInnerProgress l d i j )) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition lengthOfLIS_safety_wit_9 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) >= (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= numsSize_pre)) (PreH12 : (LISBestSoFar l i ans )) (PreH13 : (LISInnerProgress l d i j )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition lengthOfLIS_safety_wit_10 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (i: Z) (ans: Z) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = numsSize_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < numsSize_pre)) (PreH6 : (1 <= ans)) (PreH7 : (ans <= numsSize_pre)) (PreH8 : (LISBestSoFar l (i + 1 ) ans )) (PreH9 : (LISDPTablePrefix l d (i + 1 ) )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition lengthOfLIS_entail_wit_1 := 
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = numsSize_pre)) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_full dp_pre numsSize_pre )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (LISDPTablePrefix l d 0 ) ” 
  &&  “ (LISBestSoFar l 0 1 ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 0 d )
  **  (IntArray.undef_seg dp_pre 0 numsSize_pre )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = numsSize_pre)) ,
  TT && emp 
|--
  “ (LISBestSoFar l 0 1 ) ” 
  &&  “ (LISDPTablePrefix l (@nil Z) 0 ) ”
  &&  emp
).

Definition lengthOfLIS_entail_wit_1_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = numsSize_pre)) ,
  (LISBestSoFar l 0 1 )
.

Definition lengthOfLIS_entail_wit_1_split_goal_2 := 
forall (numsSize_pre: Z) (l: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = numsSize_pre)) ,
  (LISDPTablePrefix l (@nil Z) 0 )
.

Definition lengthOfLIS_entail_wit_2 := 
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= numsSize_pre)) (PreH9 : (LISDPTablePrefix l d_2 i )) (PreH10 : (LISBestSoFar l i ans )) ,
  (IntArray.seg dp_pre 0 (i + 1 ) (app (d_2) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
  **  (IntArray.full nums_pre numsSize_pre l )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= numsSize_pre) ” 
  &&  “ (LISBestSoFar l i ans ) ” 
  &&  “ (LISInnerProgress l d i 0 ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= numsSize_pre)) (PreH9 : (LISDPTablePrefix l d_2 i )) (PreH10 : (LISBestSoFar l i ans )) ,
  TT && emp 
|--
  “ (LISInnerProgress l (app (d_2) ((cons (1) ((@nil Z))))) i 0 ) ”
  &&  emp
).

Definition lengthOfLIS_entail_wit_2_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= numsSize_pre)) (PreH9 : (LISDPTablePrefix l d_2 i )) (PreH10 : (LISBestSoFar l i ans )) ,
  (LISInnerProgress l (app (d_2) ((cons (1) ((@nil Z))))) i 0 )
.

Definition lengthOfLIS_entail_wit_3_1 := 
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (((Znth (j - 0 ) d_2 0) + 1 ) > (Znth (i - 0 ) d_2 0))) (PreH2 : ((Znth j l 0) < (Znth i l 0))) (PreH3 : (j < i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= i)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= numsSize_pre)) (PreH13 : (LISBestSoFar l i ans )) (PreH14 : (LISInnerProgress l d_2 i j )) ,
  (IntArray.full dp_pre (i + 1 ) (replace_Znth (i) (((Znth (j - 0 ) d_2 0) + 1 )) (d_2)) )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= numsSize_pre) ” 
  &&  “ (LISBestSoFar l i ans ) ” 
  &&  “ (LISInnerProgress l d i (j + 1 ) ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
) \/
(
forall (dp_pre: Z) (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (((Znth (j - 0 ) d_2 0) + 1 ) > (Znth (i - 0 ) d_2 0))) (PreH2 : ((Znth j l 0) < (Znth i l 0))) (PreH3 : (j < i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= i)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= numsSize_pre)) (PreH13 : (LISBestSoFar l i ans )) (PreH14 : (LISInnerProgress l d_2 i j )) ,
  (IntArray.full dp_pre (i + 1 ) (replace_Znth (i) (((Znth (j - 0 ) d_2 0) + 1 )) (d_2)) )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= numsSize_pre) ” 
  &&  “ (LISBestSoFar l i ans ) ” 
  &&  “ (LISInnerProgress l d i (j + 1 ) ) ”
  &&  (IntArray.seg dp_pre 0 (i + 1 ) d )
).

Definition lengthOfLIS_entail_wit_3_2 := 
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (((Znth (j - 0 ) d_2 0) + 1 ) <= (Znth (i - 0 ) d_2 0))) (PreH2 : ((Znth j l 0) < (Znth i l 0))) (PreH3 : (j < i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= i)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= numsSize_pre)) (PreH13 : (LISBestSoFar l i ans )) (PreH14 : (LISInnerProgress l d_2 i j )) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d_2 )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= numsSize_pre) ” 
  &&  “ (LISBestSoFar l i ans ) ” 
  &&  “ (LISInnerProgress l d i (j + 1 ) ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (((Znth (j - 0 ) d_2 0) + 1 ) <= (Znth (i - 0 ) d_2 0))) (PreH2 : ((Znth j l 0) < (Znth i l 0))) (PreH3 : (j < i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= i)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= numsSize_pre)) (PreH13 : (LISBestSoFar l i ans )) (PreH14 : (LISInnerProgress l d_2 i j )) ,
  TT && emp 
|--
  “ (LISInnerProgress l d_2 i (j + 1 ) ) ”
  &&  emp
).

Definition lengthOfLIS_entail_wit_3_2_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (((Znth (j - 0 ) d_2 0) + 1 ) <= (Znth (i - 0 ) d_2 0))) (PreH2 : ((Znth j l 0) < (Znth i l 0))) (PreH3 : (j < i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= i)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= numsSize_pre)) (PreH13 : (LISBestSoFar l i ans )) (PreH14 : (LISInnerProgress l d_2 i j )) ,
  (LISInnerProgress l d_2 i (j + 1 ) )
.

Definition lengthOfLIS_entail_wit_3_3 := 
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) >= (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= numsSize_pre)) (PreH12 : (LISBestSoFar l i ans )) (PreH13 : (LISInnerProgress l d_2 i j )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d_2 )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= numsSize_pre) ” 
  &&  “ (LISBestSoFar l i ans ) ” 
  &&  “ (LISInnerProgress l d i (j + 1 ) ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) >= (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= numsSize_pre)) (PreH12 : (LISBestSoFar l i ans )) (PreH13 : (LISInnerProgress l d_2 i j )) ,
  TT && emp 
|--
  “ (LISInnerProgress l d_2 i (j + 1 ) ) ”
  &&  emp
).

Definition lengthOfLIS_entail_wit_3_3_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) >= (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= numsSize_pre)) (PreH12 : (LISBestSoFar l i ans )) (PreH13 : (LISInnerProgress l d_2 i j )) ,
  (LISInnerProgress l d_2 i (j + 1 ) )
.

Definition lengthOfLIS_entail_wit_4 := 
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (0 <= j)) (PreH8 : (j <= i)) (PreH9 : (1 <= ans)) (PreH10 : (ans <= numsSize_pre)) (PreH11 : (LISBestSoFar l i ans )) (PreH12 : (LISInnerProgress l d_2 i j )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d_2 )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= numsSize_pre) ” 
  &&  “ (LISBestSoFar l i ans ) ” 
  &&  “ (LISDPTablePrefix l d (i + 1 ) ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (0 <= j)) (PreH8 : (j <= i)) (PreH9 : (1 <= ans)) (PreH10 : (ans <= numsSize_pre)) (PreH11 : (LISBestSoFar l i ans )) (PreH12 : (LISInnerProgress l d_2 i j )) ,
  TT && emp 
|--
  “ (LISDPTablePrefix l d_2 (i + 1 ) ) ”
  &&  emp
).

Definition lengthOfLIS_entail_wit_4_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (0 <= j)) (PreH8 : (j <= i)) (PreH9 : (1 <= ans)) (PreH10 : (ans <= numsSize_pre)) (PreH11 : (LISBestSoFar l i ans )) (PreH12 : (LISInnerProgress l d_2 i j )) ,
  (LISDPTablePrefix l d_2 (i + 1 ) )
.

Definition lengthOfLIS_entail_wit_5_1 := 
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (i: Z) (ans: Z) (PreH1 : ((Znth (i - 0 ) d 0) > ans)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= numsSize_pre)) (PreH9 : (LISBestSoFar l i ans )) (PreH10 : (LISDPTablePrefix l d (i + 1 ) )) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (d_2: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (1 <= (Znth (i - 0 ) d 0)) ” 
  &&  “ ((Znth (i - 0 ) d 0) <= numsSize_pre) ” 
  &&  “ (LISBestSoFar l (i + 1 ) (Znth (i - 0 ) d 0) ) ” 
  &&  “ (LISDPTablePrefix l d_2 (i + 1 ) ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d_2 )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (d: (@list Z)) (i: Z) (ans: Z) (PreH1 : ((Znth (i - 0 ) d 0) > ans)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= numsSize_pre)) (PreH9 : (LISBestSoFar l i ans )) (PreH10 : (LISDPTablePrefix l d (i + 1 ) )) ,
  TT && emp 
|--
  “ (LISBestSoFar l (i + 1 ) (Znth (i - 0 ) d 0) ) ” 
  &&  “ ((Znth (i - 0 ) d 0) <= numsSize_pre) ”
  &&  emp
).

Definition lengthOfLIS_entail_wit_5_1_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (d: (@list Z)) (i: Z) (ans: Z) (PreH1 : ((Znth (i - 0 ) d 0) > ans)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= numsSize_pre)) (PreH9 : (LISBestSoFar l i ans )) (PreH10 : (LISDPTablePrefix l d (i + 1 ) )) ,
  (LISBestSoFar l (i + 1 ) (Znth (i - 0 ) d 0) )
.

Definition lengthOfLIS_entail_wit_5_1_split_goal_2 := 
forall (numsSize_pre: Z) (l: (@list Z)) (d: (@list Z)) (i: Z) (ans: Z) (PreH1 : ((Znth (i - 0 ) d 0) > ans)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= numsSize_pre)) (PreH9 : (LISBestSoFar l i ans )) (PreH10 : (LISDPTablePrefix l d (i + 1 ) )) ,
  ((Znth (i - 0 ) d 0) <= numsSize_pre)
.

Definition lengthOfLIS_entail_wit_5_2 := 
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (i: Z) (ans: Z) (PreH1 : ((Znth (i - 0 ) d_2 0) <= ans)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= numsSize_pre)) (PreH9 : (LISBestSoFar l i ans )) (PreH10 : (LISDPTablePrefix l d_2 (i + 1 ) )) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d_2 )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= numsSize_pre) ” 
  &&  “ (LISBestSoFar l (i + 1 ) ans ) ” 
  &&  “ (LISDPTablePrefix l d (i + 1 ) ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (i: Z) (ans: Z) (PreH1 : ((Znth (i - 0 ) d_2 0) <= ans)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= numsSize_pre)) (PreH9 : (LISBestSoFar l i ans )) (PreH10 : (LISDPTablePrefix l d_2 (i + 1 ) )) ,
  TT && emp 
|--
  “ (LISBestSoFar l (i + 1 ) ans ) ”
  &&  emp
).

Definition lengthOfLIS_entail_wit_5_2_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (i: Z) (ans: Z) (PreH1 : ((Znth (i - 0 ) d_2 0) <= ans)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= numsSize_pre)) (PreH9 : (LISBestSoFar l i ans )) (PreH10 : (LISDPTablePrefix l d_2 (i + 1 ) )) ,
  (LISBestSoFar l (i + 1 ) ans )
.

Definition lengthOfLIS_entail_wit_6 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (i: Z) (ans: Z) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = numsSize_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < numsSize_pre)) (PreH6 : (1 <= ans)) (PreH7 : (ans <= numsSize_pre)) (PreH8 : (LISBestSoFar l (i + 1 ) ans )) (PreH9 : (LISDPTablePrefix l d_2 (i + 1 ) )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d_2 )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= numsSize_pre) ” 
  &&  “ (LISDPTablePrefix l d (i + 1 ) ) ” 
  &&  “ (LISBestSoFar l (i + 1 ) ans ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_entail_wit_7 := 
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (i: Z) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= numsSize_pre)) (PreH9 : (LISDPTablePrefix l d_2 i )) (PreH10 : (LISBestSoFar l i ans )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 i d_2 )
  **  (IntArray.undef_seg dp_pre i numsSize_pre )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= numsSize_pre) ” 
  &&  “ (LISLength l ans ) ” 
  &&  “ (LISDPTablePrefix l d numsSize_pre ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full dp_pre numsSize_pre d )
) \/
(
forall (dp_pre: Z) (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (i: Z) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= numsSize_pre)) (PreH9 : (LISDPTablePrefix l d_2 i )) (PreH10 : (LISBestSoFar l i ans )) ,
  (IntArray.seg dp_pre 0 i d_2 )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= numsSize_pre) ” 
  &&  “ (LISLength l ans ) ” 
  &&  “ (LISDPTablePrefix l d numsSize_pre ) ”
  &&  (IntArray.full dp_pre numsSize_pre d )
).

Definition lengthOfLIS_return_wit_1 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = numsSize_pre)) (PreH4 : (1 <= ans)) (PreH5 : (ans <= numsSize_pre)) (PreH6 : (LISLength l ans )) (PreH7 : (LISDPTablePrefix l d_2 numsSize_pre )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full dp_pre numsSize_pre d_2 )
|--
  EX (d: (@list Z)) ,
  “ (LISLength l ans ) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= numsSize_pre) ” 
  &&  “ (LISDPTablePrefix l d numsSize_pre ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full dp_pre numsSize_pre d )
.

Definition lengthOfLIS_partial_solve_wit_1 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= numsSize_pre)) (PreH9 : (LISDPTablePrefix l d i )) (PreH10 : (LISBestSoFar l i ans )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 i d )
  **  (IntArray.undef_seg dp_pre i numsSize_pre )
|--
  “ (i < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= numsSize_pre) ” 
  &&  “ (LISDPTablePrefix l d i ) ” 
  &&  “ (LISBestSoFar l i ans ) ”
  &&  (((dp_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 i d )
.

Definition lengthOfLIS_partial_solve_wit_2 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (j < i)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (0 <= j)) (PreH8 : (j <= i)) (PreH9 : (1 <= ans)) (PreH10 : (ans <= numsSize_pre)) (PreH11 : (LISBestSoFar l i ans )) (PreH12 : (LISInnerProgress l d i j )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= numsSize_pre) ” 
  &&  “ (LISBestSoFar l i ans ) ” 
  &&  “ (LISInnerProgress l d i j ) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int  |-> (Znth j l 0))
  **  (IntArray.missing_i nums_pre j 0 numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_partial_solve_wit_3 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (j < i)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (0 <= j)) (PreH8 : (j <= i)) (PreH9 : (1 <= ans)) (PreH10 : (ans <= numsSize_pre)) (PreH11 : (LISBestSoFar l i ans )) (PreH12 : (LISInnerProgress l d i j )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= numsSize_pre) ” 
  &&  “ (LISBestSoFar l i ans ) ” 
  &&  “ (LISInnerProgress l d i j ) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i nums_pre i 0 numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_partial_solve_wit_4 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) < (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= numsSize_pre)) (PreH12 : (LISBestSoFar l i ans )) (PreH13 : (LISInnerProgress l d i j )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((Znth j l 0) < (Znth i l 0)) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= numsSize_pre) ” 
  &&  “ (LISBestSoFar l i ans ) ” 
  &&  “ (LISInnerProgress l d i j ) ”
  &&  (((dp_pre + (j * sizeof(INT)))) # Int  |-> (Znth (j - 0 ) d 0))
  **  (IntArray.missing_i dp_pre j 0 (i + 1 ) d )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_partial_solve_wit_5 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) < (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= numsSize_pre)) (PreH12 : (LISBestSoFar l i ans )) (PreH13 : (LISInnerProgress l d i j )) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((Znth j l 0) < (Znth i l 0)) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= numsSize_pre) ” 
  &&  “ (LISBestSoFar l i ans ) ” 
  &&  “ (LISInnerProgress l d i j ) ”
  &&  (((dp_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i - 0 ) d 0))
  **  (IntArray.missing_i dp_pre i 0 (i + 1 ) d )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_partial_solve_wit_6 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (((Znth (j - 0 ) d 0) + 1 ) > (Znth (i - 0 ) d 0))) (PreH2 : ((Znth j l 0) < (Znth i l 0))) (PreH3 : (j < i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= i)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= numsSize_pre)) (PreH13 : (LISBestSoFar l i ans )) (PreH14 : (LISInnerProgress l d i j )) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (((Znth (j - 0 ) d 0) + 1 ) > (Znth (i - 0 ) d 0)) ” 
  &&  “ ((Znth j l 0) < (Znth i l 0)) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= numsSize_pre) ” 
  &&  “ (LISBestSoFar l i ans ) ” 
  &&  “ (LISInnerProgress l d i j ) ”
  &&  (((dp_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i dp_pre i 0 (i + 1 ) d )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_partial_solve_wit_7 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (i: Z) (ans: Z) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = numsSize_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < numsSize_pre)) (PreH6 : (1 <= ans)) (PreH7 : (ans <= numsSize_pre)) (PreH8 : (LISBestSoFar l i ans )) (PreH9 : (LISDPTablePrefix l d (i + 1 ) )) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= numsSize_pre) ” 
  &&  “ (LISBestSoFar l i ans ) ” 
  &&  “ (LISDPTablePrefix l d (i + 1 ) ) ”
  &&  (((dp_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i - 0 ) d 0))
  **  (IntArray.missing_i dp_pre i 0 (i + 1 ) d )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition lengthOfLIS_partial_solve_wit_8 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (i: Z) (ans: Z) (PreH1 : ((Znth (i - 0 ) d 0) > ans)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= numsSize_pre)) (PreH9 : (LISBestSoFar l i ans )) (PreH10 : (LISDPTablePrefix l d (i + 1 ) )) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((Znth (i - 0 ) d 0) > ans) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= numsSize_pre) ” 
  &&  “ (LISBestSoFar l i ans ) ” 
  &&  “ (LISDPTablePrefix l d (i + 1 ) ) ”
  &&  (((dp_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i - 0 ) d 0))
  **  (IntArray.missing_i dp_pre i 0 (i + 1 ) d )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Module Type VC_Correct.


Axiom proof_of_lengthOfLIS_safety_wit_1 : lengthOfLIS_safety_wit_1.
Axiom proof_of_lengthOfLIS_safety_wit_2 : lengthOfLIS_safety_wit_2.
Axiom proof_of_lengthOfLIS_safety_wit_3 : lengthOfLIS_safety_wit_3.
Axiom proof_of_lengthOfLIS_safety_wit_4 : lengthOfLIS_safety_wit_4.
Axiom proof_of_lengthOfLIS_safety_wit_5 : lengthOfLIS_safety_wit_5.
Axiom proof_of_lengthOfLIS_safety_wit_6 : lengthOfLIS_safety_wit_6.
Axiom proof_of_lengthOfLIS_safety_wit_7 : lengthOfLIS_safety_wit_7.
Axiom proof_of_lengthOfLIS_safety_wit_8 : lengthOfLIS_safety_wit_8.
Axiom proof_of_lengthOfLIS_safety_wit_9 : lengthOfLIS_safety_wit_9.
Axiom proof_of_lengthOfLIS_safety_wit_10 : lengthOfLIS_safety_wit_10.
Axiom proof_of_lengthOfLIS_entail_wit_1 : lengthOfLIS_entail_wit_1.
Axiom proof_of_lengthOfLIS_entail_wit_2 : lengthOfLIS_entail_wit_2.
Axiom proof_of_lengthOfLIS_entail_wit_3_1 : lengthOfLIS_entail_wit_3_1.
Axiom proof_of_lengthOfLIS_entail_wit_3_2 : lengthOfLIS_entail_wit_3_2.
Axiom proof_of_lengthOfLIS_entail_wit_3_3 : lengthOfLIS_entail_wit_3_3.
Axiom proof_of_lengthOfLIS_entail_wit_4 : lengthOfLIS_entail_wit_4.
Axiom proof_of_lengthOfLIS_entail_wit_5_1 : lengthOfLIS_entail_wit_5_1.
Axiom proof_of_lengthOfLIS_entail_wit_5_2 : lengthOfLIS_entail_wit_5_2.
Axiom proof_of_lengthOfLIS_entail_wit_6 : lengthOfLIS_entail_wit_6.
Axiom proof_of_lengthOfLIS_entail_wit_7 : lengthOfLIS_entail_wit_7.
Axiom proof_of_lengthOfLIS_return_wit_1 : lengthOfLIS_return_wit_1.
Axiom proof_of_lengthOfLIS_partial_solve_wit_1 : lengthOfLIS_partial_solve_wit_1.
Axiom proof_of_lengthOfLIS_partial_solve_wit_2 : lengthOfLIS_partial_solve_wit_2.
Axiom proof_of_lengthOfLIS_partial_solve_wit_3 : lengthOfLIS_partial_solve_wit_3.
Axiom proof_of_lengthOfLIS_partial_solve_wit_4 : lengthOfLIS_partial_solve_wit_4.
Axiom proof_of_lengthOfLIS_partial_solve_wit_5 : lengthOfLIS_partial_solve_wit_5.
Axiom proof_of_lengthOfLIS_partial_solve_wit_6 : lengthOfLIS_partial_solve_wit_6.
Axiom proof_of_lengthOfLIS_partial_solve_wit_7 : lengthOfLIS_partial_solve_wit_7.
Axiom proof_of_lengthOfLIS_partial_solve_wit_8 : lengthOfLIS_partial_solve_wit_8.

End VC_Correct.
