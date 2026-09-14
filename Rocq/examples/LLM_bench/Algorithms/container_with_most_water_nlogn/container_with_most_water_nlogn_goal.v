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
Require Import SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_nlogn.container_with_most_water_nlogn_lib.
Local Open Scope sac.

(*----- Function mergeHeightIndexRunsNLogN -----*)

Definition mergeHeightIndexRunsNLogN_safety_wit_1 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : ((Znth i source_h 0) >= (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth i source_i 0)) (dest_i)) )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  ((( &( "sourceHeight" ) )) # Ptr  |-> sourceHeight_pre)
  **  ((( &( "sourceIndex" ) )) # Ptr  |-> sourceIndex_pre)
  **  ((( &( "destinationHeight" ) )) # Ptr  |-> destinationHeight_pre)
  **  ((( &( "destinationIndex" ) )) # Ptr  |-> destinationIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "middle" ) )) # Int  |-> middle_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "output" ) )) # Int  |-> output)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mergeHeightIndexRunsNLogN_safety_wit_2 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : ((Znth i source_h 0) < (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth j source_i 0)) (dest_i)) )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  ((( &( "sourceHeight" ) )) # Ptr  |-> sourceHeight_pre)
  **  ((( &( "sourceIndex" ) )) # Ptr  |-> sourceIndex_pre)
  **  ((( &( "destinationHeight" ) )) # Ptr  |-> destinationHeight_pre)
  **  ((( &( "destinationIndex" ) )) # Ptr  |-> destinationIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "middle" ) )) # Int  |-> middle_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "output" ) )) # Int  |-> output)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition mergeHeightIndexRunsNLogN_safety_wit_3 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : ((Znth i source_h 0) >= (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth i source_i 0)) (dest_i)) )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  ((( &( "sourceHeight" ) )) # Ptr  |-> sourceHeight_pre)
  **  ((( &( "sourceIndex" ) )) # Ptr  |-> sourceIndex_pre)
  **  ((( &( "destinationHeight" ) )) # Ptr  |-> destinationHeight_pre)
  **  ((( &( "destinationIndex" ) )) # Ptr  |-> destinationIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "middle" ) )) # Int  |-> middle_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "output" ) )) # Int  |-> output)
|--
  “ ((output + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (output + 1 )) ”
.

Definition mergeHeightIndexRunsNLogN_safety_wit_4 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : ((Znth i source_h 0) < (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth j source_i 0)) (dest_i)) )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  ((( &( "sourceHeight" ) )) # Ptr  |-> sourceHeight_pre)
  **  ((( &( "sourceIndex" ) )) # Ptr  |-> sourceIndex_pre)
  **  ((( &( "destinationHeight" ) )) # Ptr  |-> destinationHeight_pre)
  **  ((( &( "destinationIndex" ) )) # Ptr  |-> destinationIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "middle" ) )) # Int  |-> middle_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "output" ) )) # Int  |-> output)
|--
  “ ((output + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (output + 1 )) ”
.

Definition mergeHeightIndexRunsNLogN_safety_wit_5 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : (i < middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  ((( &( "sourceHeight" ) )) # Ptr  |-> sourceHeight_pre)
  **  ((( &( "sourceIndex" ) )) # Ptr  |-> sourceIndex_pre)
  **  ((( &( "destinationHeight" ) )) # Ptr  |-> destinationHeight_pre)
  **  ((( &( "destinationIndex" ) )) # Ptr  |-> destinationIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "middle" ) )) # Int  |-> middle_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "output" ) )) # Int  |-> output)
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
|--
  “ False ”
.

Definition mergeHeightIndexRunsNLogN_safety_wit_6 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (i: Z) (j: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : (i < middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (j = right_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth i source_i 0)) (dest_i)) )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  ((( &( "sourceHeight" ) )) # Ptr  |-> sourceHeight_pre)
  **  ((( &( "sourceIndex" ) )) # Ptr  |-> sourceIndex_pre)
  **  ((( &( "destinationHeight" ) )) # Ptr  |-> destinationHeight_pre)
  **  ((( &( "destinationIndex" ) )) # Ptr  |-> destinationIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "middle" ) )) # Int  |-> middle_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output" ) )) # Int  |-> output)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mergeHeightIndexRunsNLogN_safety_wit_7 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (i: Z) (j: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : (i < middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (j = right_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth i source_i 0)) (dest_i)) )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  ((( &( "sourceHeight" ) )) # Ptr  |-> sourceHeight_pre)
  **  ((( &( "sourceIndex" ) )) # Ptr  |-> sourceIndex_pre)
  **  ((( &( "destinationHeight" ) )) # Ptr  |-> destinationHeight_pre)
  **  ((( &( "destinationIndex" ) )) # Ptr  |-> destinationIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "middle" ) )) # Int  |-> middle_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "output" ) )) # Int  |-> output)
|--
  “ ((output + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (output + 1 )) ”
.

Definition mergeHeightIndexRunsNLogN_safety_wit_8 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth j source_i 0)) (dest_i)) )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  ((( &( "sourceHeight" ) )) # Ptr  |-> sourceHeight_pre)
  **  ((( &( "sourceIndex" ) )) # Ptr  |-> sourceIndex_pre)
  **  ((( &( "destinationHeight" ) )) # Ptr  |-> destinationHeight_pre)
  **  ((( &( "destinationIndex" ) )) # Ptr  |-> destinationIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "middle" ) )) # Int  |-> middle_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "output" ) )) # Int  |-> output)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition mergeHeightIndexRunsNLogN_safety_wit_9 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth j source_i 0)) (dest_i)) )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  ((( &( "sourceHeight" ) )) # Ptr  |-> sourceHeight_pre)
  **  ((( &( "sourceIndex" ) )) # Ptr  |-> sourceIndex_pre)
  **  ((( &( "destinationHeight" ) )) # Ptr  |-> destinationHeight_pre)
  **  ((( &( "destinationIndex" ) )) # Ptr  |-> destinationIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "middle" ) )) # Int  |-> middle_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "output" ) )) # Int  |-> output)
|--
  “ ((output + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (output + 1 )) ”
.

Definition mergeHeightIndexRunsNLogN_entail_wit_1 := 
(
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (PreH1 : ((Zlength (source_h)) = count_pre)) (PreH2 : ((Zlength (source_i)) = count_pre)) (PreH3 : ((Zlength (dest0_h)) = count_pre)) (PreH4 : ((Zlength (dest0_i)) = count_pre)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre <= middle_pre)) (PreH7 : (middle_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (HeightIndexRangeDescendingNLogN source_h left_pre middle_pre )) (PreH10 : (HeightIndexRangeDescendingNLogN source_h middle_pre right_pre )) ,
  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest0_h )
  **  (IntArray.full destinationIndex_pre count_pre dest0_i )
|--
  EX (dest_i: (@list Z))  (dest_h: (@list Z)) ,
  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= left_pre) ” 
  &&  “ (left_pre <= middle_pre) ” 
  &&  “ (middle_pre <= middle_pre) ” 
  &&  “ (middle_pre <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (left_pre = ((left_pre + (left_pre - left_pre ) ) + (middle_pre - middle_pre ) )) ” 
  &&  “ (left_pre <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre left_pre middle_pre left_pre ) ”
  &&  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
) \/
(
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (PreH1 : ((Zlength (source_h)) = count_pre)) (PreH2 : ((Zlength (source_i)) = count_pre)) (PreH3 : ((Zlength (dest0_h)) = count_pre)) (PreH4 : ((Zlength (dest0_i)) = count_pre)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre <= middle_pre)) (PreH7 : (middle_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (HeightIndexRangeDescendingNLogN source_h left_pre middle_pre )) (PreH10 : (HeightIndexRangeDescendingNLogN source_h middle_pre right_pre )) ,
  TT && emp 
|--
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest0_h dest0_i left_pre middle_pre right_pre left_pre middle_pre left_pre ) ”
  &&  emp
).

Definition mergeHeightIndexRunsNLogN_entail_wit_1_split_goal_1 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (PreH1 : ((Zlength (source_h)) = count_pre)) (PreH2 : ((Zlength (source_i)) = count_pre)) (PreH3 : ((Zlength (dest0_h)) = count_pre)) (PreH4 : ((Zlength (dest0_i)) = count_pre)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre <= middle_pre)) (PreH7 : (middle_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (HeightIndexRangeDescendingNLogN source_h left_pre middle_pre )) (PreH10 : (HeightIndexRangeDescendingNLogN source_h middle_pre right_pre )) ,
  (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest0_h dest0_i left_pre middle_pre right_pre left_pre middle_pre left_pre )
.

Definition mergeHeightIndexRunsNLogN_entail_wit_2_1 := 
(
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : ((Znth i source_h 0) >= (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  (IntArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth i source_i 0)) (dest_i_2)) )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h 0)) (dest_h_2)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
|--
  EX (dest_i: (@list Z))  (dest_h: (@list Z)) ,
  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ ((output + 1 ) = ((left_pre + ((i + 1 ) - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= (output + 1 )) ” 
  &&  “ ((output + 1 ) <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre (i + 1 ) j (output + 1 ) ) ”
  &&  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
) \/
(
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : ((Znth i source_h 0) >= (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  TT && emp 
|--
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i (replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth i source_h 0)) (dest_h_2)) (replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth i source_i 0)) (dest_i_2)) left_pre middle_pre right_pre (i + 1 ) j (((left_pre + (i - left_pre ) ) + (j - middle_pre ) ) + 1 ) ) ” 
  &&  “ ((Zlength ((replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth i source_i 0)) (dest_i_2)))) = count_pre) ” 
  &&  “ ((Zlength ((replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth i source_h 0)) (dest_h_2)))) = count_pre) ”
  &&  emp
).

Definition mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_1 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : ((Znth i source_h 0) >= (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  (MergePrefixStateNLogN source_h source_i dest0_h dest0_i (replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth i source_h 0)) (dest_h_2)) (replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth i source_i 0)) (dest_i_2)) left_pre middle_pre right_pre (i + 1 ) j (((left_pre + (i - left_pre ) ) + (j - middle_pre ) ) + 1 ) )
.

Definition mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_2 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : ((Znth i source_h 0) >= (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  ((Zlength ((replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth i source_i 0)) (dest_i_2)))) = count_pre)
.

Definition mergeHeightIndexRunsNLogN_entail_wit_2_1_split_goal_3 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : ((Znth i source_h 0) >= (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  ((Zlength ((replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth i source_h 0)) (dest_h_2)))) = count_pre)
.

Definition mergeHeightIndexRunsNLogN_entail_wit_2_2 := 
(
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : ((Znth i source_h 0) < (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  (IntArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth j source_i 0)) (dest_i_2)) )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h 0)) (dest_h_2)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
|--
  EX (dest_i: (@list Z))  (dest_h: (@list Z)) ,
  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ ((output + 1 ) = ((left_pre + (i - left_pre ) ) + ((j + 1 ) - middle_pre ) )) ” 
  &&  “ (left_pre <= (output + 1 )) ” 
  &&  “ ((output + 1 ) <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i (j + 1 ) (output + 1 ) ) ”
  &&  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
) \/
(
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : ((Znth i source_h 0) < (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  TT && emp 
|--
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i (replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth j source_h 0)) (dest_h_2)) (replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth j source_i 0)) (dest_i_2)) left_pre middle_pre right_pre i (j + 1 ) (((left_pre + (i - left_pre ) ) + (j - middle_pre ) ) + 1 ) ) ” 
  &&  “ ((Zlength ((replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth j source_i 0)) (dest_i_2)))) = count_pre) ” 
  &&  “ ((Zlength ((replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth j source_h 0)) (dest_h_2)))) = count_pre) ”
  &&  emp
).

Definition mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_1 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : ((Znth i source_h 0) < (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  (MergePrefixStateNLogN source_h source_i dest0_h dest0_i (replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth j source_h 0)) (dest_h_2)) (replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth j source_i 0)) (dest_i_2)) left_pre middle_pre right_pre i (j + 1 ) (((left_pre + (i - left_pre ) ) + (j - middle_pre ) ) + 1 ) )
.

Definition mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_2 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : ((Znth i source_h 0) < (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  ((Zlength ((replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth j source_i 0)) (dest_i_2)))) = count_pre)
.

Definition mergeHeightIndexRunsNLogN_entail_wit_2_2_split_goal_3 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : ((Znth i source_h 0) < (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  ((Zlength ((replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth j source_h 0)) (dest_h_2)))) = count_pre)
.

Definition mergeHeightIndexRunsNLogN_entail_wit_3_1 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : (i >= middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= i)) (PreH10 : (i <= middle_pre)) (PreH11 : (middle_pre <= j)) (PreH12 : (j <= right_pre)) (PreH13 : (right_pre <= count_pre)) (PreH14 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH15 : (left_pre <= output)) (PreH16 : (output <= right_pre)) (PreH17 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h_2 )
  **  (IntArray.full destinationIndex_pre count_pre dest_i_2 )
|--
  (EX (dest_i: (@list Z))  (dest_h: (@list Z)) ,
  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (i = middle_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i ))
  ||
  (EX (dest_i: (@list Z))  (dest_h: (@list Z)) ,
  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (j = right_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i ))
.

Definition mergeHeightIndexRunsNLogN_entail_wit_3_2 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : (j >= right_pre)) (PreH2 : (i < middle_pre)) (PreH3 : ((Zlength (source_h)) = count_pre)) (PreH4 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH5 : ((Zlength (dest0_h)) = count_pre)) (PreH6 : ((Zlength (dest0_i)) = count_pre)) (PreH7 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH8 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h_2 )
  **  (IntArray.full destinationIndex_pre count_pre dest_i_2 )
|--
  EX (dest_i: (@list Z))  (dest_h: (@list Z)) ,
  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (j = right_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
.

Definition mergeHeightIndexRunsNLogN_entail_wit_4 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (i: Z) (j: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : (i < middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (j = right_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  (IntArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth i source_i 0)) (dest_i_2)) )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h 0)) (dest_h_2)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
|--
  (EX (dest_i: (@list Z))  (dest_h: (@list Z)) ,
  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ ((i + 1 ) = middle_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ ((output + 1 ) = ((left_pre + ((i + 1 ) - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= (output + 1 )) ” 
  &&  “ ((output + 1 ) <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre (i + 1 ) j (output + 1 ) ) ”
  &&  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i ))
  ||
  (EX (dest_i: (@list Z))  (dest_h: (@list Z)) ,
  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (j = right_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ ((output + 1 ) = ((left_pre + ((i + 1 ) - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= (output + 1 )) ” 
  &&  “ ((output + 1 ) <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre (i + 1 ) j (output + 1 ) ) ”
  &&  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i ))
.

Definition mergeHeightIndexRunsNLogN_entail_wit_5_1 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : (i >= middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h_2 )
  **  (IntArray.full destinationIndex_pre count_pre dest_i_2 )
|--
  EX (dest_i: (@list Z))  (dest_h: (@list Z)) ,
  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (i = middle_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
.

Definition mergeHeightIndexRunsNLogN_entail_wit_5_2 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (i: Z) (j: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : (i >= middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (j = right_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h_2 )
  **  (IntArray.full destinationIndex_pre count_pre dest_i_2 )
|--
  EX (dest_i: (@list Z))  (dest_h: (@list Z)) ,
  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (i = middle_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
.

Definition mergeHeightIndexRunsNLogN_entail_wit_6 := 
(
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  (IntArray.full destinationIndex_pre count_pre (replace_Znth (output) ((Znth j source_i 0)) (dest_i_2)) )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h 0)) (dest_h_2)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
|--
  EX (dest_i: (@list Z))  (dest_h: (@list Z)) ,
  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (i = middle_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ ((output + 1 ) = ((left_pre + (i - left_pre ) ) + ((j + 1 ) - middle_pre ) )) ” 
  &&  “ (left_pre <= (output + 1 )) ” 
  &&  “ ((output + 1 ) <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i (j + 1 ) (output + 1 ) ) ”
  &&  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
) \/
(
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  TT && emp 
|--
  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i (replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth j source_h 0)) (dest_h_2)) (replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth j source_i 0)) (dest_i_2)) left_pre middle_pre right_pre middle_pre (j + 1 ) (((left_pre + (i - left_pre ) ) + (j - middle_pre ) ) + 1 ) ) ” 
  &&  “ ((Zlength ((replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth j source_i 0)) (dest_i_2)))) = count_pre) ” 
  &&  “ ((Zlength ((replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth j source_h 0)) (dest_h_2)))) = count_pre) ”
  &&  emp
).

Definition mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_1 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  (MergePrefixStateNLogN source_h source_i dest0_h dest0_i (replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth j source_h 0)) (dest_h_2)) (replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth j source_i 0)) (dest_i_2)) left_pre middle_pre right_pre middle_pre (j + 1 ) (((left_pre + (i - left_pre ) ) + (j - middle_pre ) ) + 1 ) )
.

Definition mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_2 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  ((Zlength ((replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth j source_i 0)) (dest_i_2)))) = count_pre)
.

Definition mergeHeightIndexRunsNLogN_entail_wit_6_split_goal_3 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  ((Zlength ((replace_Znth (((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ((Znth j source_h 0)) (dest_h_2)))) = count_pre)
.

Definition mergeHeightIndexRunsNLogN_return_wit_1 := 
(
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : (j >= right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h_2 )
  **  (IntArray.full destinationIndex_pre count_pre dest_i_2 )
|--
  EX (dest_h: (@list Z))  (dest_i: (@list Z)) ,
  “ (HeightIndexRangeMergeResultNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre ) ”
  &&  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
) \/
(
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : (j >= right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  TT && emp 
|--
  “ (HeightIndexRangeMergeResultNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre ) ”
  &&  emp
).

Definition mergeHeightIndexRunsNLogN_return_wit_1_split_goal_1 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i_2: (@list Z)) (dest_h_2: (@list Z)) (PreH1 : (j >= right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h_2)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i_2)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre i j output )) ,
  (HeightIndexRangeMergeResultNLogN source_h source_i dest0_h dest0_i dest_h_2 dest_i_2 left_pre middle_pre right_pre )
.

Definition mergeHeightIndexRunsNLogN_partial_solve_wit_1 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : (j < right_pre)) (PreH2 : (i < middle_pre)) (PreH3 : ((Zlength (source_h)) = count_pre)) (PreH4 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH5 : ((Zlength (dest0_h)) = count_pre)) (PreH6 : ((Zlength (dest0_i)) = count_pre)) (PreH7 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH8 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
|--
  “ (j < right_pre) ” 
  &&  “ (i < middle_pre) ” 
  &&  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (((sourceHeight_pre + (i * sizeof(INT)))) # Int  |-> (Znth i source_h 0))
  **  (IntArray.missing_i sourceHeight_pre i 0 count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
.

Definition mergeHeightIndexRunsNLogN_partial_solve_wit_2 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : (j < right_pre)) (PreH2 : (i < middle_pre)) (PreH3 : ((Zlength (source_h)) = count_pre)) (PreH4 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH5 : ((Zlength (dest0_h)) = count_pre)) (PreH6 : ((Zlength (dest0_i)) = count_pre)) (PreH7 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH8 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
|--
  “ (j < right_pre) ” 
  &&  “ (i < middle_pre) ” 
  &&  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (((sourceHeight_pre + (j * sizeof(INT)))) # Int  |-> (Znth j source_h 0))
  **  (IntArray.missing_i sourceHeight_pre j 0 count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
.

Definition mergeHeightIndexRunsNLogN_partial_solve_wit_3 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : ((Znth i source_h 0) >= (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
|--
  “ ((Znth i source_h 0) >= (Znth j source_h 0)) ” 
  &&  “ (j < right_pre) ” 
  &&  “ (i < middle_pre) ” 
  &&  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (((sourceHeight_pre + (i * sizeof(INT)))) # Int  |-> (Znth i source_h 0))
  **  (IntArray.missing_i sourceHeight_pre i 0 count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
.

Definition mergeHeightIndexRunsNLogN_partial_solve_wit_4 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : ((Znth i source_h 0) >= (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
|--
  “ ((Znth i source_h 0) >= (Znth j source_h 0)) ” 
  &&  “ (j < right_pre) ” 
  &&  “ (i < middle_pre) ” 
  &&  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (((destinationHeight_pre + (output * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i destinationHeight_pre output 0 count_pre dest_h )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
.

Definition mergeHeightIndexRunsNLogN_partial_solve_wit_5 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : ((Znth i source_h 0) >= (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
|--
  “ ((Znth i source_h 0) >= (Znth j source_h 0)) ” 
  &&  “ (j < right_pre) ” 
  &&  “ (i < middle_pre) ” 
  &&  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (((sourceIndex_pre + (i * sizeof(INT)))) # Int  |-> (Znth i source_i 0))
  **  (IntArray.missing_i sourceIndex_pre i 0 count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
.

Definition mergeHeightIndexRunsNLogN_partial_solve_wit_6 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : ((Znth i source_h 0) >= (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
|--
  “ ((Znth i source_h 0) >= (Znth j source_h 0)) ” 
  &&  “ (j < right_pre) ” 
  &&  “ (i < middle_pre) ” 
  &&  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (((destinationIndex_pre + (output * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i destinationIndex_pre output 0 count_pre dest_i )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
.

Definition mergeHeightIndexRunsNLogN_partial_solve_wit_7 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : ((Znth i source_h 0) < (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
|--
  “ ((Znth i source_h 0) < (Znth j source_h 0)) ” 
  &&  “ (j < right_pre) ” 
  &&  “ (i < middle_pre) ” 
  &&  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (((sourceHeight_pre + (j * sizeof(INT)))) # Int  |-> (Znth j source_h 0))
  **  (IntArray.missing_i sourceHeight_pre j 0 count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
.

Definition mergeHeightIndexRunsNLogN_partial_solve_wit_8 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : ((Znth i source_h 0) < (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
|--
  “ ((Znth i source_h 0) < (Znth j source_h 0)) ” 
  &&  “ (j < right_pre) ” 
  &&  “ (i < middle_pre) ” 
  &&  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (((destinationHeight_pre + (output * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i destinationHeight_pre output 0 count_pre dest_h )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
.

Definition mergeHeightIndexRunsNLogN_partial_solve_wit_9 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : ((Znth i source_h 0) < (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
|--
  “ ((Znth i source_h 0) < (Znth j source_h 0)) ” 
  &&  “ (j < right_pre) ” 
  &&  “ (i < middle_pre) ” 
  &&  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (((sourceIndex_pre + (j * sizeof(INT)))) # Int  |-> (Znth j source_i 0))
  **  (IntArray.missing_i sourceIndex_pre j 0 count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
.

Definition mergeHeightIndexRunsNLogN_partial_solve_wit_10 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : ((Znth i source_h 0) < (Znth j source_h 0))) (PreH2 : (j < right_pre)) (PreH3 : (i < middle_pre)) (PreH4 : ((Zlength (source_h)) = count_pre)) (PreH5 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH6 : ((Zlength (dest0_h)) = count_pre)) (PreH7 : ((Zlength (dest0_i)) = count_pre)) (PreH8 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH9 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= middle_pre)) (PreH13 : (middle_pre <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (right_pre <= count_pre)) (PreH16 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH17 : (left_pre <= output)) (PreH18 : (output <= right_pre)) (PreH19 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
|--
  “ ((Znth i source_h 0) < (Znth j source_h 0)) ” 
  &&  “ (j < right_pre) ” 
  &&  “ (i < middle_pre) ” 
  &&  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (((destinationIndex_pre + (output * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i destinationIndex_pre output 0 count_pre dest_i )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
.

Definition mergeHeightIndexRunsNLogN_partial_solve_wit_11 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (i: Z) (j: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : (i < middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (j = right_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
|--
  “ (i < middle_pre) ” 
  &&  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (j = right_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (((sourceHeight_pre + (i * sizeof(INT)))) # Int  |-> (Znth i source_h 0))
  **  (IntArray.missing_i sourceHeight_pre i 0 count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
.

Definition mergeHeightIndexRunsNLogN_partial_solve_wit_12 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (i: Z) (j: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : (i < middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (j = right_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
|--
  “ (i < middle_pre) ” 
  &&  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (j = right_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (((destinationHeight_pre + (output * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i destinationHeight_pre output 0 count_pre dest_h )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
.

Definition mergeHeightIndexRunsNLogN_partial_solve_wit_13 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (i: Z) (j: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : (i < middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (j = right_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
|--
  “ (i < middle_pre) ” 
  &&  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (j = right_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (((sourceIndex_pre + (i * sizeof(INT)))) # Int  |-> (Znth i source_i 0))
  **  (IntArray.missing_i sourceIndex_pre i 0 count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
.

Definition mergeHeightIndexRunsNLogN_partial_solve_wit_14 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (i: Z) (j: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : (i < middle_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (j = right_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
|--
  “ (i < middle_pre) ” 
  &&  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (j = right_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (((destinationIndex_pre + (output * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i destinationIndex_pre output 0 count_pre dest_i )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth i source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
.

Definition mergeHeightIndexRunsNLogN_partial_solve_wit_15 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
|--
  “ (j < right_pre) ” 
  &&  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (i = middle_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (((sourceHeight_pre + (j * sizeof(INT)))) # Int  |-> (Znth j source_h 0))
  **  (IntArray.missing_i sourceHeight_pre j 0 count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
.

Definition mergeHeightIndexRunsNLogN_partial_solve_wit_16 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre dest_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
|--
  “ (j < right_pre) ” 
  &&  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (i = middle_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (((destinationHeight_pre + (output * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i destinationHeight_pre output 0 count_pre dest_h )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
.

Definition mergeHeightIndexRunsNLogN_partial_solve_wit_17 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
|--
  “ (j < right_pre) ” 
  &&  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (i = middle_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (((sourceIndex_pre + (j * sizeof(INT)))) # Int  |-> (Znth j source_i 0))
  **  (IntArray.missing_i sourceIndex_pre j 0 count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
.

Definition mergeHeightIndexRunsNLogN_partial_solve_wit_18 := 
forall (right_pre: Z) (middle_pre: Z) (left_pre: Z) (count_pre: Z) (destinationIndex_pre: Z) (destinationHeight_pre: Z) (sourceIndex_pre: Z) (sourceHeight_pre: Z) (dest0_i: (@list Z)) (dest0_h: (@list Z)) (source_i: (@list Z)) (source_h: (@list Z)) (output: Z) (j: Z) (i: Z) (dest_i: (@list Z)) (dest_h: (@list Z)) (PreH1 : (j < right_pre)) (PreH2 : ((Zlength (source_h)) = count_pre)) (PreH3 : ((Zlength (source_i)) = (Zlength (source_h)))) (PreH4 : ((Zlength (dest0_h)) = count_pre)) (PreH5 : ((Zlength (dest0_i)) = count_pre)) (PreH6 : ((Zlength (dest_h)) = (Zlength (dest0_h)))) (PreH7 : ((Zlength (dest_i)) = (Zlength (dest0_i)))) (PreH8 : (i = middle_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= i)) (PreH11 : (i <= middle_pre)) (PreH12 : (middle_pre <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (right_pre <= count_pre)) (PreH15 : (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) ))) (PreH16 : (left_pre <= output)) (PreH17 : (output <= right_pre)) (PreH18 : (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output )) ,
  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
  **  (IntArray.full destinationIndex_pre count_pre dest_i )
|--
  “ (j < right_pre) ” 
  &&  “ ((Zlength (source_h)) = count_pre) ” 
  &&  “ ((Zlength (source_i)) = (Zlength (source_h))) ” 
  &&  “ ((Zlength (dest0_h)) = count_pre) ” 
  &&  “ ((Zlength (dest0_i)) = count_pre) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (dest0_h))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (dest0_i))) ” 
  &&  “ (i = middle_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= middle_pre) ” 
  &&  “ (middle_pre <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (output = ((left_pre + (i - left_pre ) ) + (j - middle_pre ) )) ” 
  &&  “ (left_pre <= output) ” 
  &&  “ (output <= right_pre) ” 
  &&  “ (MergePrefixStateNLogN source_h source_i dest0_h dest0_i dest_h dest_i left_pre middle_pre right_pre i j output ) ”
  &&  (((destinationIndex_pre + (output * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i destinationIndex_pre output 0 count_pre dest_i )
  **  (IntArray.full sourceIndex_pre count_pre source_i )
  **  (IntArray.full destinationHeight_pre count_pre (replace_Znth (output) ((Znth j source_h 0)) (dest_h)) )
  **  (IntArray.full sourceHeight_pre count_pre source_h )
.

(*----- Function sortHeightIndexRangeNLogN -----*)

Definition sortHeightIndexRangeNLogN_safety_wit_1 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (PreH1 : ((Zlength (work0_h)) = count_pre)) (PreH2 : ((Zlength (work0_i)) = count_pre)) (PreH3 : ((Zlength (buffer0_h)) = count_pre)) (PreH4 : ((Zlength (buffer0_i)) = count_pre)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre <= right_pre)) (PreH7 : (right_pre <= count_pre)) (PreH8 : (count_pre <= 100000)) ,
  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full workHeight_pre count_pre work0_h )
  **  (IntArray.full workIndex_pre count_pre work0_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer0_i )
|--
  “ ((right_pre - left_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (right_pre - left_pre )) ”
.

Definition sortHeightIndexRangeNLogN_safety_wit_2 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (PreH1 : ((Zlength (work0_h)) = count_pre)) (PreH2 : ((Zlength (work0_i)) = count_pre)) (PreH3 : ((Zlength (buffer0_h)) = count_pre)) (PreH4 : ((Zlength (buffer0_i)) = count_pre)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre <= right_pre)) (PreH7 : (right_pre <= count_pre)) (PreH8 : (count_pre <= 100000)) ,
  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full workHeight_pre count_pre work0_h )
  **  (IntArray.full workIndex_pre count_pre work0_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer0_i )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sortHeightIndexRangeNLogN_safety_wit_3 := 
(
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (PreH1 : ((right_pre - left_pre ) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int  |->_)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full workHeight_pre count_pre work0_h )
  **  (IntArray.full workIndex_pre count_pre work0_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer0_i )
|--
  “ ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left_pre + ((right_pre - left_pre ) ÷ 2 ) )) ”
) \/
(
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (PreH1 : ((right_pre - left_pre ) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int  |->_)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full workHeight_pre count_pre work0_h )
  **  (IntArray.full workIndex_pre count_pre work0_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer0_i )
|--
  “ ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left_pre + ((right_pre - left_pre ) ÷ 2 ) )) ”
).

Definition sortHeightIndexRangeNLogN_safety_wit_3_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (PreH1 : ((right_pre - left_pre ) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int  |->_)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full workHeight_pre count_pre work0_h )
  **  (IntArray.full workIndex_pre count_pre work0_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer0_i )
|--
  “ ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= INT_MAX) ”
.

Definition sortHeightIndexRangeNLogN_safety_wit_3_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (PreH1 : ((right_pre - left_pre ) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int  |->_)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full workHeight_pre count_pre work0_h )
  **  (IntArray.full workIndex_pre count_pre work0_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer0_i )
|--
  “ ((INT_MIN) <= (left_pre + ((right_pre - left_pre ) ÷ 2 ) )) ”
.

Definition sortHeightIndexRangeNLogN_safety_wit_4 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (PreH1 : ((right_pre - left_pre ) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int  |->_)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full workHeight_pre count_pre work0_h )
  **  (IntArray.full workIndex_pre count_pre work0_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer0_i )
|--
  “ (((right_pre - left_pre ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition sortHeightIndexRangeNLogN_safety_wit_5 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (PreH1 : ((right_pre - left_pre ) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int  |->_)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full workHeight_pre count_pre work0_h )
  **  (IntArray.full workIndex_pre count_pre work0_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer0_i )
|--
  “ ((right_pre - left_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (right_pre - left_pre )) ”
.

Definition sortHeightIndexRangeNLogN_safety_wit_6 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (PreH1 : ((right_pre - left_pre ) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int  |->_)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full workHeight_pre count_pre work0_h )
  **  (IntArray.full workIndex_pre count_pre work0_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer0_i )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sortHeightIndexRangeNLogN_safety_wit_7 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (work0_i: (@list Z)) (work0_h: (@list Z)) (buffer0_h: (@list Z)) (buffer0_i: (@list Z)) (k: Z) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_i1: (@list Z)) (work_h1: (@list Z)) (work_i: (@list Z)) (work_h: (@list Z)) (work_mid_i: (@list Z)) (work_mid_h: (@list Z)) (middle: Z) (PreH1 : (k < right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h)) = count_pre)) (PreH6 : ((Zlength (work_mid_i)) = count_pre)) (PreH7 : ((Zlength (work_h)) = count_pre)) (PreH8 : ((Zlength (work_i)) = count_pre)) (PreH9 : ((Zlength (work_h1)) = count_pre)) (PreH10 : ((Zlength (work_i1)) = count_pre)) (PreH11 : ((Zlength (buffer_h)) = count_pre)) (PreH12 : ((Zlength (buffer_i)) = count_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle )) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre )) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre )) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre k )) ,
  (IntArray.full workIndex_pre count_pre (replace_Znth (k) ((Znth k buffer_i 0)) (work_i1)) )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
  **  (IntArray.full workHeight_pre count_pre (replace_Znth (k) ((Znth k buffer_h 0)) (work_h1)) )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "middle" ) )) # Int  |-> middle)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition sortHeightIndexRangeNLogN_entail_wit_1 := 
(
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (work_h_2: (@list Z)) (work_i_2: (@list Z)) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (work_h_3: (@list Z)) (work_i_3: (@list Z)) (PreH1 : (HeightIndexRangeSortResultNLogN work_h_2 work_i_2 work_h_3 work_i_3 (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) right_pre )) (PreH2 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h_2 work_i_2 left_pre (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) )) (PreH3 : ((right_pre - left_pre ) > 1)) (PreH4 : ((Zlength (work0_h)) = count_pre)) (PreH5 : ((Zlength (work0_i)) = count_pre)) (PreH6 : ((Zlength (buffer0_h)) = count_pre)) (PreH7 : ((Zlength (buffer0_i)) = count_pre)) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre <= count_pre)) (PreH11 : (count_pre <= 100000)) ,
  (IntArray.full workHeight_pre count_pre work_h_3 )
  **  (IntArray.full workIndex_pre count_pre work_i_3 )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (work_i: (@list Z))  (work_h: (@list Z))  (work_mid_i: (@list Z))  (work_mid_h: (@list Z)) ,
  “ (count_pre <= 100000) ” 
  &&  “ (left_pre < (left_pre + ((right_pre - left_pre ) ÷ 2 ) )) ” 
  &&  “ ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) < right_pre) ” 
  &&  “ ((Zlength (work_mid_h)) = count_pre) ” 
  &&  “ ((Zlength (work_mid_i)) = count_pre) ” 
  &&  “ ((Zlength (work_h)) = count_pre) ” 
  &&  “ ((Zlength (work_i)) = count_pre) ” 
  &&  “ ((Zlength (buffer_h)) = count_pre) ” 
  &&  “ ((Zlength (buffer_i)) = count_pre) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) ) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) right_pre ) ” 
  &&  “ (HeightIndexRangeDescendingNLogN work_h left_pre (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) ) ” 
  &&  “ (HeightIndexRangeDescendingNLogN work_h (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) right_pre ) ”
  &&  (IntArray.full workHeight_pre count_pre work_h )
  **  (IntArray.full workIndex_pre count_pre work_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
) \/
(
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (work_h_2: (@list Z)) (work_i_2: (@list Z)) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (work_h_3: (@list Z)) (work_i_3: (@list Z)) (PreH1 : (HeightIndexRangeSortResultNLogN work_h_2 work_i_2 work_h_3 work_i_3 (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) right_pre )) (PreH2 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h_2 work_i_2 left_pre (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) )) (PreH3 : ((right_pre - left_pre ) > 1)) (PreH4 : ((Zlength (work0_h)) = count_pre)) (PreH5 : ((Zlength (work0_i)) = count_pre)) (PreH6 : ((Zlength (buffer0_h)) = count_pre)) (PreH7 : ((Zlength (buffer0_i)) = count_pre)) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre <= count_pre)) (PreH11 : (count_pre <= 100000)) ,
  TT && emp 
|--
  EX (work_mid_i: (@list Z))  (work_mid_h: (@list Z)) ,
  “ (left_pre < (left_pre + ((right_pre - left_pre ) ÷ 2 ) )) ” 
  &&  “ ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) < right_pre) ” 
  &&  “ ((Zlength (work_mid_h)) = (Zlength (work0_h))) ” 
  &&  “ ((Zlength (work_mid_i)) = (Zlength (work0_h))) ” 
  &&  “ ((Zlength (work_h_3)) = (Zlength (work0_h))) ” 
  &&  “ ((Zlength (work_i_3)) = (Zlength (work0_h))) ” 
  &&  “ ((Zlength (buffer_h_2)) = (Zlength (work0_h))) ” 
  &&  “ ((Zlength (buffer_i_2)) = (Zlength (work0_h))) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) ) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h_3 work_i_3 (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) right_pre ) ” 
  &&  “ (HeightIndexRangeDescendingNLogN work_h_3 left_pre (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) ) ” 
  &&  “ (HeightIndexRangeDescendingNLogN work_h_3 (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) right_pre ) ”
  &&  emp
).

Definition sortHeightIndexRangeNLogN_entail_wit_2 := 
(
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (work0_i: (@list Z)) (work0_h: (@list Z)) (work_mid_h_2: (@list Z)) (work_mid_i_2: (@list Z)) (work_h_2: (@list Z)) (work_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (middle: Z) (dest_h: (@list Z)) (dest_i: (@list Z)) (PreH1 : (HeightIndexRangeMergeResultNLogN work_h_2 work_i_2 buffer_h_2 buffer_i_2 dest_h dest_i left_pre middle right_pre )) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h_2)) = count_pre)) (PreH6 : ((Zlength (work_mid_i_2)) = count_pre)) (PreH7 : ((Zlength (work_h_2)) = count_pre)) (PreH8 : ((Zlength (work_i_2)) = count_pre)) (PreH9 : ((Zlength (buffer_h_2)) = count_pre)) (PreH10 : ((Zlength (buffer_i_2)) = count_pre)) (PreH11 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h_2 work_mid_i_2 left_pre middle )) (PreH12 : (HeightIndexRangeSortResultNLogN work_mid_h_2 work_mid_i_2 work_h_2 work_i_2 middle right_pre )) (PreH13 : (HeightIndexRangeDescendingNLogN work_h_2 left_pre middle )) (PreH14 : (HeightIndexRangeDescendingNLogN work_h_2 middle right_pre )) ,
  (IntArray.full workHeight_pre count_pre work_h_2 )
  **  (IntArray.full workIndex_pre count_pre work_i_2 )
  **  (IntArray.full bufferHeight_pre count_pre dest_h )
  **  (IntArray.full bufferIndex_pre count_pre dest_i )
|--
  EX (buffer0_h: (@list Z))  (buffer0_i: (@list Z))  (buffer_i: (@list Z))  (buffer_h: (@list Z))  (work_i: (@list Z))  (work_h: (@list Z))  (work_mid_i: (@list Z))  (work_mid_h: (@list Z)) ,
  “ (count_pre <= 100000) ” 
  &&  “ (left_pre < middle) ” 
  &&  “ (middle < right_pre) ” 
  &&  “ ((Zlength (work_mid_h)) = count_pre) ” 
  &&  “ ((Zlength (work_mid_i)) = count_pre) ” 
  &&  “ ((Zlength (work_h)) = count_pre) ” 
  &&  “ ((Zlength (work_i)) = count_pre) ” 
  &&  “ ((Zlength (buffer_h)) = count_pre) ” 
  &&  “ ((Zlength (buffer_i)) = count_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle ) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre ) ” 
  &&  “ (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre ) ”
  &&  (IntArray.full workHeight_pre count_pre work_h )
  **  (IntArray.full workIndex_pre count_pre work_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
) \/
(
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (work0_i: (@list Z)) (work0_h: (@list Z)) (work_mid_h_2: (@list Z)) (work_mid_i_2: (@list Z)) (work_h_2: (@list Z)) (work_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (middle: Z) (dest_h: (@list Z)) (dest_i: (@list Z)) (PreH1 : (HeightIndexRangeMergeResultNLogN work_h_2 work_i_2 buffer_h_2 buffer_i_2 dest_h dest_i left_pre middle right_pre )) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h_2)) = count_pre)) (PreH6 : ((Zlength (work_mid_i_2)) = count_pre)) (PreH7 : ((Zlength (work_h_2)) = count_pre)) (PreH8 : ((Zlength (work_i_2)) = count_pre)) (PreH9 : ((Zlength (buffer_h_2)) = count_pre)) (PreH10 : ((Zlength (buffer_i_2)) = count_pre)) (PreH11 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h_2 work_mid_i_2 left_pre middle )) (PreH12 : (HeightIndexRangeSortResultNLogN work_mid_h_2 work_mid_i_2 work_h_2 work_i_2 middle right_pre )) (PreH13 : (HeightIndexRangeDescendingNLogN work_h_2 left_pre middle )) (PreH14 : (HeightIndexRangeDescendingNLogN work_h_2 middle right_pre )) ,
  TT && emp 
|--
  EX (work_mid_i: (@list Z))  (work_mid_h: (@list Z)) ,
  “ ((Zlength (work_mid_h)) = (Zlength (work_mid_h_2))) ” 
  &&  “ ((Zlength (work_mid_i)) = (Zlength (work_mid_h_2))) ” 
  &&  “ ((Zlength (dest_h)) = (Zlength (work_mid_h_2))) ” 
  &&  “ ((Zlength (dest_i)) = (Zlength (work_mid_h_2))) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (right_pre <= (Zlength (work_mid_h_2))) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle ) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h_2 work_i_2 middle right_pre ) ”
  &&  emp
).

Definition sortHeightIndexRangeNLogN_entail_wit_3 := 
(
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (work0_i: (@list Z)) (work0_h: (@list Z)) (work_mid_h_2: (@list Z)) (work_mid_i_2: (@list Z)) (work_h_2: (@list Z)) (work_i_2: (@list Z)) (buffer0_h_2: (@list Z)) (buffer0_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (middle: Z) (PreH1 : (count_pre <= 100000)) (PreH2 : (left_pre < middle)) (PreH3 : (middle < right_pre)) (PreH4 : ((Zlength (work_mid_h_2)) = count_pre)) (PreH5 : ((Zlength (work_mid_i_2)) = count_pre)) (PreH6 : ((Zlength (work_h_2)) = count_pre)) (PreH7 : ((Zlength (work_i_2)) = count_pre)) (PreH8 : ((Zlength (buffer_h_2)) = count_pre)) (PreH9 : ((Zlength (buffer_i_2)) = count_pre)) (PreH10 : (0 <= left_pre)) (PreH11 : (right_pre <= count_pre)) (PreH12 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h_2 work_mid_i_2 left_pre middle )) (PreH13 : (HeightIndexRangeSortResultNLogN work_mid_h_2 work_mid_i_2 work_h_2 work_i_2 middle right_pre )) (PreH14 : (HeightIndexRangeMergeResultNLogN work_h_2 work_i_2 buffer0_h_2 buffer0_i_2 buffer_h_2 buffer_i_2 left_pre middle right_pre )) ,
  (IntArray.full workHeight_pre count_pre work_h_2 )
  **  (IntArray.full workIndex_pre count_pre work_i_2 )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i_2 )
|--
  EX (buffer0_h: (@list Z))  (buffer0_i: (@list Z))  (buffer_i: (@list Z))  (buffer_h: (@list Z))  (work_i1: (@list Z))  (work_h1: (@list Z))  (work_i: (@list Z))  (work_h: (@list Z))  (work_mid_i: (@list Z))  (work_mid_h: (@list Z)) ,
  “ (count_pre <= 100000) ” 
  &&  “ (left_pre < middle) ” 
  &&  “ (middle < right_pre) ” 
  &&  “ ((Zlength (work_mid_h)) = count_pre) ” 
  &&  “ ((Zlength (work_mid_i)) = count_pre) ” 
  &&  “ ((Zlength (work_h)) = count_pre) ” 
  &&  “ ((Zlength (work_i)) = count_pre) ” 
  &&  “ ((Zlength (work_h1)) = count_pre) ” 
  &&  “ ((Zlength (work_i1)) = count_pre) ” 
  &&  “ ((Zlength (buffer_h)) = count_pre) ” 
  &&  “ ((Zlength (buffer_i)) = count_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle ) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre ) ” 
  &&  “ (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre ) ” 
  &&  “ (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre left_pre ) ”
  &&  (IntArray.full workHeight_pre count_pre work_h1 )
  **  (IntArray.full workIndex_pre count_pre work_i1 )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
) \/
(
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (work0_i: (@list Z)) (work0_h: (@list Z)) (work_mid_h_2: (@list Z)) (work_mid_i_2: (@list Z)) (work_h_2: (@list Z)) (work_i_2: (@list Z)) (buffer0_h_2: (@list Z)) (buffer0_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (middle: Z) (PreH1 : (count_pre <= 100000)) (PreH2 : (left_pre < middle)) (PreH3 : (middle < right_pre)) (PreH4 : ((Zlength (work_mid_h_2)) = count_pre)) (PreH5 : ((Zlength (work_mid_i_2)) = count_pre)) (PreH6 : ((Zlength (work_h_2)) = count_pre)) (PreH7 : ((Zlength (work_i_2)) = count_pre)) (PreH8 : ((Zlength (buffer_h_2)) = count_pre)) (PreH9 : ((Zlength (buffer_i_2)) = count_pre)) (PreH10 : (0 <= left_pre)) (PreH11 : (right_pre <= count_pre)) (PreH12 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h_2 work_mid_i_2 left_pre middle )) (PreH13 : (HeightIndexRangeSortResultNLogN work_mid_h_2 work_mid_i_2 work_h_2 work_i_2 middle right_pre )) (PreH14 : (HeightIndexRangeMergeResultNLogN work_h_2 work_i_2 buffer0_h_2 buffer0_i_2 buffer_h_2 buffer_i_2 left_pre middle right_pre )) ,
  TT && emp 
|--
  EX (buffer0_h: (@list Z))  (buffer0_i: (@list Z))  (work_i: (@list Z))  (work_h: (@list Z))  (work_mid_i: (@list Z))  (work_mid_h: (@list Z)) ,
  “ ((Zlength (work_mid_h)) = (Zlength (work_mid_h_2))) ” 
  &&  “ ((Zlength (work_mid_i)) = (Zlength (work_mid_h_2))) ” 
  &&  “ ((Zlength (work_h)) = (Zlength (work_mid_h_2))) ” 
  &&  “ ((Zlength (work_i)) = (Zlength (work_mid_h_2))) ” 
  &&  “ (left_pre <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle ) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre ) ” 
  &&  “ (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h_2 buffer_i_2 left_pre middle right_pre ) ” 
  &&  “ (CopyHeightIndexPrefixNLogN buffer_h_2 buffer_i_2 work_h work_i work_h_2 work_i_2 left_pre right_pre left_pre ) ”
  &&  emp
).

Definition sortHeightIndexRangeNLogN_entail_wit_4 := 
(
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (work0_i: (@list Z)) (work0_h: (@list Z)) (buffer0_h_2: (@list Z)) (buffer0_i_2: (@list Z)) (k: Z) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (work_i1_2: (@list Z)) (work_h1_2: (@list Z)) (work_i_2: (@list Z)) (work_h_2: (@list Z)) (work_mid_i_2: (@list Z)) (work_mid_h_2: (@list Z)) (middle: Z) (PreH1 : (k < right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h_2)) = count_pre)) (PreH6 : ((Zlength (work_mid_i_2)) = count_pre)) (PreH7 : ((Zlength (work_h_2)) = count_pre)) (PreH8 : ((Zlength (work_i_2)) = count_pre)) (PreH9 : ((Zlength (work_h1_2)) = count_pre)) (PreH10 : ((Zlength (work_i1_2)) = count_pre)) (PreH11 : ((Zlength (buffer_h_2)) = count_pre)) (PreH12 : ((Zlength (buffer_i_2)) = count_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h_2 work_mid_i_2 left_pre middle )) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h_2 work_mid_i_2 work_h_2 work_i_2 middle right_pre )) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h_2 work_i_2 buffer0_h_2 buffer0_i_2 buffer_h_2 buffer_i_2 left_pre middle right_pre )) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h_2 buffer_i_2 work_h_2 work_i_2 work_h1_2 work_i1_2 left_pre right_pre k )) ,
  (IntArray.full workIndex_pre count_pre (replace_Znth (k) ((Znth k buffer_i_2 0)) (work_i1_2)) )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i_2 )
  **  (IntArray.full workHeight_pre count_pre (replace_Znth (k) ((Znth k buffer_h_2 0)) (work_h1_2)) )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h_2 )
|--
  EX (buffer0_h: (@list Z))  (buffer0_i: (@list Z))  (buffer_i: (@list Z))  (buffer_h: (@list Z))  (work_i1: (@list Z))  (work_h1: (@list Z))  (work_i: (@list Z))  (work_h: (@list Z))  (work_mid_i: (@list Z))  (work_mid_h: (@list Z)) ,
  “ (count_pre <= 100000) ” 
  &&  “ (left_pre < middle) ” 
  &&  “ (middle < right_pre) ” 
  &&  “ ((Zlength (work_mid_h)) = count_pre) ” 
  &&  “ ((Zlength (work_mid_i)) = count_pre) ” 
  &&  “ ((Zlength (work_h)) = count_pre) ” 
  &&  “ ((Zlength (work_i)) = count_pre) ” 
  &&  “ ((Zlength (work_h1)) = count_pre) ” 
  &&  “ ((Zlength (work_i1)) = count_pre) ” 
  &&  “ ((Zlength (buffer_h)) = count_pre) ” 
  &&  “ ((Zlength (buffer_i)) = count_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle ) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre ) ” 
  &&  “ (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre ) ” 
  &&  “ (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre (k + 1 ) ) ”
  &&  (IntArray.full workHeight_pre count_pre work_h1 )
  **  (IntArray.full workIndex_pre count_pre work_i1 )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
) \/
(
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (work0_i: (@list Z)) (work0_h: (@list Z)) (buffer0_h_2: (@list Z)) (buffer0_i_2: (@list Z)) (k: Z) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (work_i1_2: (@list Z)) (work_h1_2: (@list Z)) (work_i_2: (@list Z)) (work_h_2: (@list Z)) (work_mid_i_2: (@list Z)) (work_mid_h_2: (@list Z)) (middle: Z) (PreH1 : (k < right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h_2)) = count_pre)) (PreH6 : ((Zlength (work_mid_i_2)) = count_pre)) (PreH7 : ((Zlength (work_h_2)) = count_pre)) (PreH8 : ((Zlength (work_i_2)) = count_pre)) (PreH9 : ((Zlength (work_h1_2)) = count_pre)) (PreH10 : ((Zlength (work_i1_2)) = count_pre)) (PreH11 : ((Zlength (buffer_h_2)) = count_pre)) (PreH12 : ((Zlength (buffer_i_2)) = count_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h_2 work_mid_i_2 left_pre middle )) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h_2 work_mid_i_2 work_h_2 work_i_2 middle right_pre )) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h_2 work_i_2 buffer0_h_2 buffer0_i_2 buffer_h_2 buffer_i_2 left_pre middle right_pre )) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h_2 buffer_i_2 work_h_2 work_i_2 work_h1_2 work_i1_2 left_pre right_pre k )) ,
  TT && emp 
|--
  EX (buffer0_h: (@list Z))  (buffer0_i: (@list Z))  (work_i: (@list Z))  (work_h: (@list Z))  (work_mid_i: (@list Z))  (work_mid_h: (@list Z)) ,
  “ ((Zlength (work_mid_h)) = (Zlength (work_mid_h_2))) ” 
  &&  “ ((Zlength (work_mid_i)) = (Zlength (work_mid_h_2))) ” 
  &&  “ ((Zlength (work_h)) = (Zlength (work_mid_h_2))) ” 
  &&  “ ((Zlength (work_i)) = (Zlength (work_mid_h_2))) ” 
  &&  “ ((Zlength ((replace_Znth (k) ((Znth k buffer_h_2 0)) (work_h1_2)))) = (Zlength (work_mid_h_2))) ” 
  &&  “ ((Zlength ((replace_Znth (k) ((Znth k buffer_i_2 0)) (work_i1_2)))) = (Zlength (work_mid_h_2))) ” 
  &&  “ (left_pre <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= right_pre) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle ) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre ) ” 
  &&  “ (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h_2 buffer_i_2 left_pre middle right_pre ) ” 
  &&  “ (CopyHeightIndexPrefixNLogN buffer_h_2 buffer_i_2 work_h work_i (replace_Znth (k) ((Znth k buffer_h_2 0)) (work_h1_2)) (replace_Znth (k) ((Znth k buffer_i_2 0)) (work_i1_2)) left_pre right_pre (k + 1 ) ) ”
  &&  emp
).

Definition sortHeightIndexRangeNLogN_return_wit_1 := 
(
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (PreH1 : ((right_pre - left_pre ) <= 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  (IntArray.full workHeight_pre count_pre work0_h )
  **  (IntArray.full workIndex_pre count_pre work0_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer0_i )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (work_h: (@list Z))  (work_i: (@list Z)) ,
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre right_pre ) ”
  &&  (IntArray.full workHeight_pre count_pre work_h )
  **  (IntArray.full workIndex_pre count_pre work_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
) \/
(
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (PreH1 : ((right_pre - left_pre ) <= 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  TT && emp 
|--
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work0_h work0_i left_pre right_pre ) ”
  &&  emp
).

Definition sortHeightIndexRangeNLogN_return_wit_1_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (PreH1 : ((right_pre - left_pre ) <= 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  (HeightIndexRangeSortResultNLogN work0_h work0_i work0_h work0_i left_pre right_pre )
.

Definition sortHeightIndexRangeNLogN_return_wit_2 := 
(
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (work0_i: (@list Z)) (work0_h: (@list Z)) (buffer0_h: (@list Z)) (buffer0_i: (@list Z)) (k: Z) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (work_i1: (@list Z)) (work_h1: (@list Z)) (work_i_2: (@list Z)) (work_h_2: (@list Z)) (work_mid_i: (@list Z)) (work_mid_h: (@list Z)) (middle: Z) (PreH1 : (k >= right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h)) = count_pre)) (PreH6 : ((Zlength (work_mid_i)) = count_pre)) (PreH7 : ((Zlength (work_h_2)) = count_pre)) (PreH8 : ((Zlength (work_i_2)) = count_pre)) (PreH9 : ((Zlength (work_h1)) = count_pre)) (PreH10 : ((Zlength (work_i1)) = count_pre)) (PreH11 : ((Zlength (buffer_h_2)) = count_pre)) (PreH12 : ((Zlength (buffer_i_2)) = count_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle )) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h_2 work_i_2 middle right_pre )) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h_2 work_i_2 buffer0_h buffer0_i buffer_h_2 buffer_i_2 left_pre middle right_pre )) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h_2 buffer_i_2 work_h_2 work_i_2 work_h1 work_i1 left_pre right_pre k )) ,
  (IntArray.full workHeight_pre count_pre work_h1 )
  **  (IntArray.full workIndex_pre count_pre work_i1 )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (work_h: (@list Z))  (work_i: (@list Z)) ,
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre right_pre ) ”
  &&  (IntArray.full workHeight_pre count_pre work_h )
  **  (IntArray.full workIndex_pre count_pre work_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
) \/
(
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (work0_i: (@list Z)) (work0_h: (@list Z)) (buffer0_h: (@list Z)) (buffer0_i: (@list Z)) (k: Z) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (work_i1: (@list Z)) (work_h1: (@list Z)) (work_i_2: (@list Z)) (work_h_2: (@list Z)) (work_mid_i: (@list Z)) (work_mid_h: (@list Z)) (middle: Z) (PreH1 : (k >= right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h)) = count_pre)) (PreH6 : ((Zlength (work_mid_i)) = count_pre)) (PreH7 : ((Zlength (work_h_2)) = count_pre)) (PreH8 : ((Zlength (work_i_2)) = count_pre)) (PreH9 : ((Zlength (work_h1)) = count_pre)) (PreH10 : ((Zlength (work_i1)) = count_pre)) (PreH11 : ((Zlength (buffer_h_2)) = count_pre)) (PreH12 : ((Zlength (buffer_i_2)) = count_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle )) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h_2 work_i_2 middle right_pre )) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h_2 work_i_2 buffer0_h buffer0_i buffer_h_2 buffer_i_2 left_pre middle right_pre )) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h_2 buffer_i_2 work_h_2 work_i_2 work_h1 work_i1 left_pre right_pre k )) ,
  TT && emp 
|--
  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_h1 work_i1 left_pre right_pre ) ”
  &&  emp
).

Definition sortHeightIndexRangeNLogN_return_wit_2_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (work0_i: (@list Z)) (work0_h: (@list Z)) (buffer0_h: (@list Z)) (buffer0_i: (@list Z)) (k: Z) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (work_i1: (@list Z)) (work_h1: (@list Z)) (work_i_2: (@list Z)) (work_h_2: (@list Z)) (work_mid_i: (@list Z)) (work_mid_h: (@list Z)) (middle: Z) (PreH1 : (k >= right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h)) = count_pre)) (PreH6 : ((Zlength (work_mid_i)) = count_pre)) (PreH7 : ((Zlength (work_h_2)) = count_pre)) (PreH8 : ((Zlength (work_i_2)) = count_pre)) (PreH9 : ((Zlength (work_h1)) = count_pre)) (PreH10 : ((Zlength (work_i1)) = count_pre)) (PreH11 : ((Zlength (buffer_h_2)) = count_pre)) (PreH12 : ((Zlength (buffer_i_2)) = count_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle )) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h_2 work_i_2 middle right_pre )) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h_2 work_i_2 buffer0_h buffer0_i buffer_h_2 buffer_i_2 left_pre middle right_pre )) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h_2 buffer_i_2 work_h_2 work_i_2 work_h1 work_i1 left_pre right_pre k )) ,
  (HeightIndexRangeSortResultNLogN work0_h work0_i work_h1 work_i1 left_pre right_pre )
.

Definition sortHeightIndexRangeNLogN_partial_solve_wit_1_pure := 
(
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (PreH1 : ((right_pre - left_pre ) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int  |-> (left_pre + ((right_pre - left_pre ) ÷ 2 ) ))
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full workHeight_pre count_pre work0_h )
  **  (IntArray.full workIndex_pre count_pre work0_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer0_i )
|--
  “ ((Zlength (work0_h)) = count_pre) ” 
  &&  “ ((Zlength (work0_i)) = count_pre) ” 
  &&  “ ((Zlength (buffer0_h)) = count_pre) ” 
  &&  “ ((Zlength (buffer0_i)) = count_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (count_pre <= 100000) ” 
  &&  “ ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= count_pre) ” 
  &&  “ (left_pre <= (left_pre + ((right_pre - left_pre ) ÷ 2 ) )) ”
) \/
(
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) >= INT_MIN)) (PreH9 : ((right_pre - left_pre ) > 1)) (PreH10 : ((Zlength (work0_h)) = count_pre)) (PreH11 : ((Zlength (work0_i)) = count_pre)) (PreH12 : ((Zlength (buffer0_h)) = count_pre)) (PreH13 : ((Zlength (buffer0_i)) = count_pre)) (PreH14 : (0 <= left_pre)) (PreH15 : (left_pre <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int  |-> (left_pre + ((right_pre - left_pre ) ÷ 2 ) ))
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full workHeight_pre count_pre work0_h )
  **  (IntArray.full workIndex_pre count_pre work0_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer0_i )
|--
  “ (left_pre <= (left_pre + ((right_pre - left_pre ) ÷ 2 ) )) ” 
  &&  “ ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= count_pre) ”
).

Definition sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) >= INT_MIN)) (PreH9 : ((right_pre - left_pre ) > 1)) (PreH10 : ((Zlength (work0_h)) = count_pre)) (PreH11 : ((Zlength (work0_i)) = count_pre)) (PreH12 : ((Zlength (buffer0_h)) = count_pre)) (PreH13 : ((Zlength (buffer0_i)) = count_pre)) (PreH14 : (0 <= left_pre)) (PreH15 : (left_pre <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int  |-> (left_pre + ((right_pre - left_pre ) ÷ 2 ) ))
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full workHeight_pre count_pre work0_h )
  **  (IntArray.full workIndex_pre count_pre work0_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer0_i )
|--
  “ (left_pre <= (left_pre + ((right_pre - left_pre ) ÷ 2 ) )) ”
.

Definition sortHeightIndexRangeNLogN_partial_solve_wit_1_pure_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) >= INT_MIN)) (PreH9 : ((right_pre - left_pre ) > 1)) (PreH10 : ((Zlength (work0_h)) = count_pre)) (PreH11 : ((Zlength (work0_i)) = count_pre)) (PreH12 : ((Zlength (buffer0_h)) = count_pre)) (PreH13 : ((Zlength (buffer0_i)) = count_pre)) (PreH14 : (0 <= left_pre)) (PreH15 : (left_pre <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (count_pre <= 100000)) ,
  ((( &( "middle" ) )) # Int  |-> (left_pre + ((right_pre - left_pre ) ÷ 2 ) ))
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full workHeight_pre count_pre work0_h )
  **  (IntArray.full workIndex_pre count_pre work0_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer0_i )
|--
  “ ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= count_pre) ”
.

Definition sortHeightIndexRangeNLogN_partial_solve_wit_1_aux := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (PreH1 : ((right_pre - left_pre ) > 1)) (PreH2 : ((Zlength (work0_h)) = count_pre)) (PreH3 : ((Zlength (work0_i)) = count_pre)) (PreH4 : ((Zlength (buffer0_h)) = count_pre)) (PreH5 : ((Zlength (buffer0_i)) = count_pre)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre <= count_pre)) (PreH9 : (count_pre <= 100000)) ,
  (IntArray.full workHeight_pre count_pre work0_h )
  **  (IntArray.full workIndex_pre count_pre work0_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer0_i )
|--
  “ ((Zlength (work0_h)) = count_pre) ” 
  &&  “ ((Zlength (work0_i)) = count_pre) ” 
  &&  “ ((Zlength (buffer0_h)) = count_pre) ” 
  &&  “ ((Zlength (buffer0_i)) = count_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (count_pre <= 100000) ” 
  &&  “ ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= count_pre) ” 
  &&  “ (left_pre <= (left_pre + ((right_pre - left_pre ) ÷ 2 ) )) ” 
  &&  “ ((right_pre - left_pre ) > 1) ” 
  &&  “ ((Zlength (work0_h)) = count_pre) ” 
  &&  “ ((Zlength (work0_i)) = count_pre) ” 
  &&  “ ((Zlength (buffer0_h)) = count_pre) ” 
  &&  “ ((Zlength (buffer0_i)) = count_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (count_pre <= 100000) ”
  &&  (IntArray.full workHeight_pre count_pre work0_h )
  **  (IntArray.full workIndex_pre count_pre work0_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer0_i )
.

Definition sortHeightIndexRangeNLogN_partial_solve_wit_1 := sortHeightIndexRangeNLogN_partial_solve_wit_1_pure -> sortHeightIndexRangeNLogN_partial_solve_wit_1_aux.

Definition sortHeightIndexRangeNLogN_partial_solve_wit_2_pure := 
(
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_h: (@list Z)) (work_i: (@list Z)) (PreH1 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) )) (PreH2 : ((right_pre - left_pre ) > 1)) (PreH3 : ((Zlength (work0_h)) = count_pre)) (PreH4 : ((Zlength (work0_i)) = count_pre)) (PreH5 : ((Zlength (buffer0_h)) = count_pre)) (PreH6 : ((Zlength (buffer0_i)) = count_pre)) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre <= count_pre)) (PreH10 : (count_pre <= 100000)) ,
  (IntArray.full workHeight_pre count_pre work_h )
  **  (IntArray.full workIndex_pre count_pre work_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
  **  ((( &( "middle" ) )) # Int  |-> (left_pre + ((right_pre - left_pre ) ÷ 2 ) ))
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (right_pre <= count_pre) ” 
  &&  “ (count_pre <= 100000) ” 
  &&  “ ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= right_pre) ” 
  &&  “ (0 <= (left_pre + ((right_pre - left_pre ) ÷ 2 ) )) ” 
  &&  “ ((Zlength (buffer_i)) = count_pre) ” 
  &&  “ ((Zlength (buffer_h)) = count_pre) ” 
  &&  “ ((Zlength (work_i)) = count_pre) ” 
  &&  “ ((Zlength (work_h)) = count_pre) ”
) \/
(
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_h: (@list Z)) (work_i: (@list Z)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) )) (PreH10 : ((right_pre - left_pre ) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (IntArray.full workHeight_pre count_pre work_h )
  **  (IntArray.full workIndex_pre count_pre work_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
  **  ((( &( "middle" ) )) # Int  |-> (left_pre + ((right_pre - left_pre ) ÷ 2 ) ))
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((Zlength (work_h)) = count_pre) ” 
  &&  “ ((Zlength (work_i)) = count_pre) ” 
  &&  “ ((Zlength (buffer_h)) = count_pre) ” 
  &&  “ ((Zlength (buffer_i)) = count_pre) ” 
  &&  “ (0 <= (left_pre + ((right_pre - left_pre ) ÷ 2 ) )) ” 
  &&  “ ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= right_pre) ”
).

Definition sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_h: (@list Z)) (work_i: (@list Z)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) )) (PreH10 : ((right_pre - left_pre ) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (IntArray.full workHeight_pre count_pre work_h )
  **  (IntArray.full workIndex_pre count_pre work_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
  **  ((( &( "middle" ) )) # Int  |-> (left_pre + ((right_pre - left_pre ) ÷ 2 ) ))
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((Zlength (work_h)) = count_pre) ”
.

Definition sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_h: (@list Z)) (work_i: (@list Z)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) )) (PreH10 : ((right_pre - left_pre ) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (IntArray.full workHeight_pre count_pre work_h )
  **  (IntArray.full workIndex_pre count_pre work_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
  **  ((( &( "middle" ) )) # Int  |-> (left_pre + ((right_pre - left_pre ) ÷ 2 ) ))
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((Zlength (work_i)) = count_pre) ”
.

Definition sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_h: (@list Z)) (work_i: (@list Z)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) )) (PreH10 : ((right_pre - left_pre ) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (IntArray.full workHeight_pre count_pre work_h )
  **  (IntArray.full workIndex_pre count_pre work_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
  **  ((( &( "middle" ) )) # Int  |-> (left_pre + ((right_pre - left_pre ) ÷ 2 ) ))
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((Zlength (buffer_h)) = count_pre) ”
.

Definition sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_4 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_h: (@list Z)) (work_i: (@list Z)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) )) (PreH10 : ((right_pre - left_pre ) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (IntArray.full workHeight_pre count_pre work_h )
  **  (IntArray.full workIndex_pre count_pre work_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
  **  ((( &( "middle" ) )) # Int  |-> (left_pre + ((right_pre - left_pre ) ÷ 2 ) ))
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((Zlength (buffer_i)) = count_pre) ”
.

Definition sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_5 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_h: (@list Z)) (work_i: (@list Z)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) )) (PreH10 : ((right_pre - left_pre ) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (IntArray.full workHeight_pre count_pre work_h )
  **  (IntArray.full workIndex_pre count_pre work_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
  **  ((( &( "middle" ) )) # Int  |-> (left_pre + ((right_pre - left_pre ) ÷ 2 ) ))
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (0 <= (left_pre + ((right_pre - left_pre ) ÷ 2 ) )) ”
.

Definition sortHeightIndexRangeNLogN_partial_solve_wit_2_pure_split_goal_6 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_h: (@list Z)) (work_i: (@list Z)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) >= INT_MIN)) (PreH9 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) )) (PreH10 : ((right_pre - left_pre ) > 1)) (PreH11 : ((Zlength (work0_h)) = count_pre)) (PreH12 : ((Zlength (work0_i)) = count_pre)) (PreH13 : ((Zlength (buffer0_h)) = count_pre)) (PreH14 : ((Zlength (buffer0_i)) = count_pre)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= right_pre)) (PreH17 : (right_pre <= count_pre)) (PreH18 : (count_pre <= 100000)) ,
  (IntArray.full workHeight_pre count_pre work_h )
  **  (IntArray.full workIndex_pre count_pre work_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
  **  ((( &( "middle" ) )) # Int  |-> (left_pre + ((right_pre - left_pre ) ÷ 2 ) ))
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= right_pre) ”
.

Definition sortHeightIndexRangeNLogN_partial_solve_wit_2_aux := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (buffer0_i: (@list Z)) (buffer0_h: (@list Z)) (work0_i: (@list Z)) (work0_h: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_h: (@list Z)) (work_i: (@list Z)) (PreH1 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) )) (PreH2 : ((right_pre - left_pre ) > 1)) (PreH3 : ((Zlength (work0_h)) = count_pre)) (PreH4 : ((Zlength (work0_i)) = count_pre)) (PreH5 : ((Zlength (buffer0_h)) = count_pre)) (PreH6 : ((Zlength (buffer0_i)) = count_pre)) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre <= count_pre)) (PreH10 : (count_pre <= 100000)) ,
  (IntArray.full workHeight_pre count_pre work_h )
  **  (IntArray.full workIndex_pre count_pre work_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
|--
  “ (right_pre <= count_pre) ” 
  &&  “ (count_pre <= 100000) ” 
  &&  “ ((left_pre + ((right_pre - left_pre ) ÷ 2 ) ) <= right_pre) ” 
  &&  “ (0 <= (left_pre + ((right_pre - left_pre ) ÷ 2 ) )) ” 
  &&  “ ((Zlength (buffer_i)) = count_pre) ” 
  &&  “ ((Zlength (buffer_h)) = count_pre) ” 
  &&  “ ((Zlength (work_i)) = count_pre) ” 
  &&  “ ((Zlength (work_h)) = count_pre) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i left_pre (left_pre + ((right_pre - left_pre ) ÷ 2 ) ) ) ” 
  &&  “ ((right_pre - left_pre ) > 1) ” 
  &&  “ ((Zlength (work0_h)) = count_pre) ” 
  &&  “ ((Zlength (work0_i)) = count_pre) ” 
  &&  “ ((Zlength (buffer0_h)) = count_pre) ” 
  &&  “ ((Zlength (buffer0_i)) = count_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (count_pre <= 100000) ”
  &&  (IntArray.full workHeight_pre count_pre work_h )
  **  (IntArray.full workIndex_pre count_pre work_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
.

Definition sortHeightIndexRangeNLogN_partial_solve_wit_2 := sortHeightIndexRangeNLogN_partial_solve_wit_2_pure -> sortHeightIndexRangeNLogN_partial_solve_wit_2_aux.

Definition sortHeightIndexRangeNLogN_partial_solve_wit_3_pure := 
(
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (work0_i: (@list Z)) (work0_h: (@list Z)) (work_mid_h: (@list Z)) (work_mid_i: (@list Z)) (work_h: (@list Z)) (work_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (middle: Z) (PreH1 : (count_pre <= 100000)) (PreH2 : (left_pre < middle)) (PreH3 : (middle < right_pre)) (PreH4 : ((Zlength (work_mid_h)) = count_pre)) (PreH5 : ((Zlength (work_mid_i)) = count_pre)) (PreH6 : ((Zlength (work_h)) = count_pre)) (PreH7 : ((Zlength (work_i)) = count_pre)) (PreH8 : ((Zlength (buffer_h)) = count_pre)) (PreH9 : ((Zlength (buffer_i)) = count_pre)) (PreH10 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle )) (PreH11 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre )) (PreH12 : (HeightIndexRangeDescendingNLogN work_h left_pre middle )) (PreH13 : (HeightIndexRangeDescendingNLogN work_h middle right_pre )) ,
  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "middle" ) )) # Int  |-> middle)
  **  (IntArray.full workHeight_pre count_pre work_h )
  **  (IntArray.full workIndex_pre count_pre work_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
|--
  “ ((Zlength (work_h)) = count_pre) ” 
  &&  “ ((Zlength (work_i)) = count_pre) ” 
  &&  “ ((Zlength (buffer_h)) = count_pre) ” 
  &&  “ ((Zlength (buffer_i)) = count_pre) ” 
  &&  “ (left_pre <= middle) ” 
  &&  “ (middle <= right_pre) ” 
  &&  “ (HeightIndexRangeDescendingNLogN work_h left_pre middle ) ” 
  &&  “ (HeightIndexRangeDescendingNLogN work_h middle right_pre ) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (0 <= left_pre) ”
) \/
(
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (work0_i: (@list Z)) (work0_h: (@list Z)) (work_mid_h: (@list Z)) (work_mid_i: (@list Z)) (work_h: (@list Z)) (work_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (middle: Z) (PreH1 : (middle <= INT_MAX)) (PreH2 : (right_pre <= INT_MAX)) (PreH3 : (left_pre <= INT_MAX)) (PreH4 : (count_pre <= INT_MAX)) (PreH5 : (middle >= INT_MIN)) (PreH6 : (right_pre >= INT_MIN)) (PreH7 : (left_pre >= INT_MIN)) (PreH8 : (count_pre >= INT_MIN)) (PreH9 : (count_pre <= 100000)) (PreH10 : (left_pre < middle)) (PreH11 : (middle < right_pre)) (PreH12 : ((Zlength (work_mid_h)) = count_pre)) (PreH13 : ((Zlength (work_mid_i)) = count_pre)) (PreH14 : ((Zlength (work_h)) = count_pre)) (PreH15 : ((Zlength (work_i)) = count_pre)) (PreH16 : ((Zlength (buffer_h)) = count_pre)) (PreH17 : ((Zlength (buffer_i)) = count_pre)) (PreH18 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle )) (PreH19 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre )) (PreH20 : (HeightIndexRangeDescendingNLogN work_h left_pre middle )) (PreH21 : (HeightIndexRangeDescendingNLogN work_h middle right_pre )) ,
  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "middle" ) )) # Int  |-> middle)
  **  (IntArray.full workHeight_pre count_pre work_h )
  **  (IntArray.full workIndex_pre count_pre work_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
|--
  “ (0 <= left_pre) ” 
  &&  “ (right_pre <= count_pre) ”
).

Definition sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (work0_i: (@list Z)) (work0_h: (@list Z)) (work_mid_h: (@list Z)) (work_mid_i: (@list Z)) (work_h: (@list Z)) (work_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (middle: Z) (PreH1 : (middle <= INT_MAX)) (PreH2 : (right_pre <= INT_MAX)) (PreH3 : (left_pre <= INT_MAX)) (PreH4 : (count_pre <= INT_MAX)) (PreH5 : (middle >= INT_MIN)) (PreH6 : (right_pre >= INT_MIN)) (PreH7 : (left_pre >= INT_MIN)) (PreH8 : (count_pre >= INT_MIN)) (PreH9 : (count_pre <= 100000)) (PreH10 : (left_pre < middle)) (PreH11 : (middle < right_pre)) (PreH12 : ((Zlength (work_mid_h)) = count_pre)) (PreH13 : ((Zlength (work_mid_i)) = count_pre)) (PreH14 : ((Zlength (work_h)) = count_pre)) (PreH15 : ((Zlength (work_i)) = count_pre)) (PreH16 : ((Zlength (buffer_h)) = count_pre)) (PreH17 : ((Zlength (buffer_i)) = count_pre)) (PreH18 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle )) (PreH19 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre )) (PreH20 : (HeightIndexRangeDescendingNLogN work_h left_pre middle )) (PreH21 : (HeightIndexRangeDescendingNLogN work_h middle right_pre )) ,
  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "middle" ) )) # Int  |-> middle)
  **  (IntArray.full workHeight_pre count_pre work_h )
  **  (IntArray.full workIndex_pre count_pre work_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
|--
  “ (0 <= left_pre) ”
.

Definition sortHeightIndexRangeNLogN_partial_solve_wit_3_pure_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (work0_i: (@list Z)) (work0_h: (@list Z)) (work_mid_h: (@list Z)) (work_mid_i: (@list Z)) (work_h: (@list Z)) (work_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (middle: Z) (PreH1 : (middle <= INT_MAX)) (PreH2 : (right_pre <= INT_MAX)) (PreH3 : (left_pre <= INT_MAX)) (PreH4 : (count_pre <= INT_MAX)) (PreH5 : (middle >= INT_MIN)) (PreH6 : (right_pre >= INT_MIN)) (PreH7 : (left_pre >= INT_MIN)) (PreH8 : (count_pre >= INT_MIN)) (PreH9 : (count_pre <= 100000)) (PreH10 : (left_pre < middle)) (PreH11 : (middle < right_pre)) (PreH12 : ((Zlength (work_mid_h)) = count_pre)) (PreH13 : ((Zlength (work_mid_i)) = count_pre)) (PreH14 : ((Zlength (work_h)) = count_pre)) (PreH15 : ((Zlength (work_i)) = count_pre)) (PreH16 : ((Zlength (buffer_h)) = count_pre)) (PreH17 : ((Zlength (buffer_i)) = count_pre)) (PreH18 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle )) (PreH19 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre )) (PreH20 : (HeightIndexRangeDescendingNLogN work_h left_pre middle )) (PreH21 : (HeightIndexRangeDescendingNLogN work_h middle right_pre )) ,
  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "middle" ) )) # Int  |-> middle)
  **  (IntArray.full workHeight_pre count_pre work_h )
  **  (IntArray.full workIndex_pre count_pre work_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
|--
  “ (right_pre <= count_pre) ”
.

Definition sortHeightIndexRangeNLogN_partial_solve_wit_3_aux := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (work0_i: (@list Z)) (work0_h: (@list Z)) (work_mid_h: (@list Z)) (work_mid_i: (@list Z)) (work_h: (@list Z)) (work_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (middle: Z) (PreH1 : (count_pre <= 100000)) (PreH2 : (left_pre < middle)) (PreH3 : (middle < right_pre)) (PreH4 : ((Zlength (work_mid_h)) = count_pre)) (PreH5 : ((Zlength (work_mid_i)) = count_pre)) (PreH6 : ((Zlength (work_h)) = count_pre)) (PreH7 : ((Zlength (work_i)) = count_pre)) (PreH8 : ((Zlength (buffer_h)) = count_pre)) (PreH9 : ((Zlength (buffer_i)) = count_pre)) (PreH10 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle )) (PreH11 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre )) (PreH12 : (HeightIndexRangeDescendingNLogN work_h left_pre middle )) (PreH13 : (HeightIndexRangeDescendingNLogN work_h middle right_pre )) ,
  (IntArray.full workHeight_pre count_pre work_h )
  **  (IntArray.full workIndex_pre count_pre work_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
|--
  “ ((Zlength (work_h)) = count_pre) ” 
  &&  “ ((Zlength (work_i)) = count_pre) ” 
  &&  “ ((Zlength (buffer_h)) = count_pre) ” 
  &&  “ ((Zlength (buffer_i)) = count_pre) ” 
  &&  “ (left_pre <= middle) ” 
  &&  “ (middle <= right_pre) ” 
  &&  “ (HeightIndexRangeDescendingNLogN work_h left_pre middle ) ” 
  &&  “ (HeightIndexRangeDescendingNLogN work_h middle right_pre ) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (count_pre <= 100000) ” 
  &&  “ (left_pre < middle) ” 
  &&  “ (middle < right_pre) ” 
  &&  “ ((Zlength (work_mid_h)) = count_pre) ” 
  &&  “ ((Zlength (work_mid_i)) = count_pre) ” 
  &&  “ ((Zlength (work_h)) = count_pre) ” 
  &&  “ ((Zlength (work_i)) = count_pre) ” 
  &&  “ ((Zlength (buffer_h)) = count_pre) ” 
  &&  “ ((Zlength (buffer_i)) = count_pre) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle ) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre ) ” 
  &&  “ (HeightIndexRangeDescendingNLogN work_h left_pre middle ) ” 
  &&  “ (HeightIndexRangeDescendingNLogN work_h middle right_pre ) ”
  &&  (IntArray.full workHeight_pre count_pre work_h )
  **  (IntArray.full workIndex_pre count_pre work_i )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
.

Definition sortHeightIndexRangeNLogN_partial_solve_wit_3 := sortHeightIndexRangeNLogN_partial_solve_wit_3_pure -> sortHeightIndexRangeNLogN_partial_solve_wit_3_aux.

Definition sortHeightIndexRangeNLogN_partial_solve_wit_4 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (work0_i: (@list Z)) (work0_h: (@list Z)) (buffer0_h: (@list Z)) (buffer0_i: (@list Z)) (k: Z) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_i1: (@list Z)) (work_h1: (@list Z)) (work_i: (@list Z)) (work_h: (@list Z)) (work_mid_i: (@list Z)) (work_mid_h: (@list Z)) (middle: Z) (PreH1 : (k < right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h)) = count_pre)) (PreH6 : ((Zlength (work_mid_i)) = count_pre)) (PreH7 : ((Zlength (work_h)) = count_pre)) (PreH8 : ((Zlength (work_i)) = count_pre)) (PreH9 : ((Zlength (work_h1)) = count_pre)) (PreH10 : ((Zlength (work_i1)) = count_pre)) (PreH11 : ((Zlength (buffer_h)) = count_pre)) (PreH12 : ((Zlength (buffer_i)) = count_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle )) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre )) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre )) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre k )) ,
  (IntArray.full workHeight_pre count_pre work_h1 )
  **  (IntArray.full workIndex_pre count_pre work_i1 )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
|--
  “ (k < right_pre) ” 
  &&  “ (count_pre <= 100000) ” 
  &&  “ (left_pre < middle) ” 
  &&  “ (middle < right_pre) ” 
  &&  “ ((Zlength (work_mid_h)) = count_pre) ” 
  &&  “ ((Zlength (work_mid_i)) = count_pre) ” 
  &&  “ ((Zlength (work_h)) = count_pre) ” 
  &&  “ ((Zlength (work_i)) = count_pre) ” 
  &&  “ ((Zlength (work_h1)) = count_pre) ” 
  &&  “ ((Zlength (work_i1)) = count_pre) ” 
  &&  “ ((Zlength (buffer_h)) = count_pre) ” 
  &&  “ ((Zlength (buffer_i)) = count_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= k) ” 
  &&  “ (k <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle ) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre ) ” 
  &&  “ (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre ) ” 
  &&  “ (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre k ) ”
  &&  (((bufferHeight_pre + (k * sizeof(INT)))) # Int  |-> (Znth k buffer_h 0))
  **  (IntArray.missing_i bufferHeight_pre k 0 count_pre buffer_h )
  **  (IntArray.full workHeight_pre count_pre work_h1 )
  **  (IntArray.full workIndex_pre count_pre work_i1 )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
.

Definition sortHeightIndexRangeNLogN_partial_solve_wit_5 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (work0_i: (@list Z)) (work0_h: (@list Z)) (buffer0_h: (@list Z)) (buffer0_i: (@list Z)) (k: Z) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_i1: (@list Z)) (work_h1: (@list Z)) (work_i: (@list Z)) (work_h: (@list Z)) (work_mid_i: (@list Z)) (work_mid_h: (@list Z)) (middle: Z) (PreH1 : (k < right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h)) = count_pre)) (PreH6 : ((Zlength (work_mid_i)) = count_pre)) (PreH7 : ((Zlength (work_h)) = count_pre)) (PreH8 : ((Zlength (work_i)) = count_pre)) (PreH9 : ((Zlength (work_h1)) = count_pre)) (PreH10 : ((Zlength (work_i1)) = count_pre)) (PreH11 : ((Zlength (buffer_h)) = count_pre)) (PreH12 : ((Zlength (buffer_i)) = count_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle )) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre )) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre )) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre k )) ,
  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full workHeight_pre count_pre work_h1 )
  **  (IntArray.full workIndex_pre count_pre work_i1 )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
|--
  “ (k < right_pre) ” 
  &&  “ (count_pre <= 100000) ” 
  &&  “ (left_pre < middle) ” 
  &&  “ (middle < right_pre) ” 
  &&  “ ((Zlength (work_mid_h)) = count_pre) ” 
  &&  “ ((Zlength (work_mid_i)) = count_pre) ” 
  &&  “ ((Zlength (work_h)) = count_pre) ” 
  &&  “ ((Zlength (work_i)) = count_pre) ” 
  &&  “ ((Zlength (work_h1)) = count_pre) ” 
  &&  “ ((Zlength (work_i1)) = count_pre) ” 
  &&  “ ((Zlength (buffer_h)) = count_pre) ” 
  &&  “ ((Zlength (buffer_i)) = count_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= k) ” 
  &&  “ (k <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle ) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre ) ” 
  &&  “ (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre ) ” 
  &&  “ (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre k ) ”
  &&  (((workHeight_pre + (k * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i workHeight_pre k 0 count_pre work_h1 )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full workIndex_pre count_pre work_i1 )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
.

Definition sortHeightIndexRangeNLogN_partial_solve_wit_6 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (work0_i: (@list Z)) (work0_h: (@list Z)) (buffer0_h: (@list Z)) (buffer0_i: (@list Z)) (k: Z) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_i1: (@list Z)) (work_h1: (@list Z)) (work_i: (@list Z)) (work_h: (@list Z)) (work_mid_i: (@list Z)) (work_mid_h: (@list Z)) (middle: Z) (PreH1 : (k < right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h)) = count_pre)) (PreH6 : ((Zlength (work_mid_i)) = count_pre)) (PreH7 : ((Zlength (work_h)) = count_pre)) (PreH8 : ((Zlength (work_i)) = count_pre)) (PreH9 : ((Zlength (work_h1)) = count_pre)) (PreH10 : ((Zlength (work_i1)) = count_pre)) (PreH11 : ((Zlength (buffer_h)) = count_pre)) (PreH12 : ((Zlength (buffer_i)) = count_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle )) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre )) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre )) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre k )) ,
  (IntArray.full workHeight_pre count_pre (replace_Znth (k) ((Znth k buffer_h 0)) (work_h1)) )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full workIndex_pre count_pre work_i1 )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
|--
  “ (k < right_pre) ” 
  &&  “ (count_pre <= 100000) ” 
  &&  “ (left_pre < middle) ” 
  &&  “ (middle < right_pre) ” 
  &&  “ ((Zlength (work_mid_h)) = count_pre) ” 
  &&  “ ((Zlength (work_mid_i)) = count_pre) ” 
  &&  “ ((Zlength (work_h)) = count_pre) ” 
  &&  “ ((Zlength (work_i)) = count_pre) ” 
  &&  “ ((Zlength (work_h1)) = count_pre) ” 
  &&  “ ((Zlength (work_i1)) = count_pre) ” 
  &&  “ ((Zlength (buffer_h)) = count_pre) ” 
  &&  “ ((Zlength (buffer_i)) = count_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= k) ” 
  &&  “ (k <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle ) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre ) ” 
  &&  “ (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre ) ” 
  &&  “ (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre k ) ”
  &&  (((bufferIndex_pre + (k * sizeof(INT)))) # Int  |-> (Znth k buffer_i 0))
  **  (IntArray.missing_i bufferIndex_pre k 0 count_pre buffer_i )
  **  (IntArray.full workHeight_pre count_pre (replace_Znth (k) ((Znth k buffer_h 0)) (work_h1)) )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full workIndex_pre count_pre work_i1 )
.

Definition sortHeightIndexRangeNLogN_partial_solve_wit_7 := 
forall (right_pre: Z) (left_pre: Z) (count_pre: Z) (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (work0_i: (@list Z)) (work0_h: (@list Z)) (buffer0_h: (@list Z)) (buffer0_i: (@list Z)) (k: Z) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_i1: (@list Z)) (work_h1: (@list Z)) (work_i: (@list Z)) (work_h: (@list Z)) (work_mid_i: (@list Z)) (work_mid_h: (@list Z)) (middle: Z) (PreH1 : (k < right_pre)) (PreH2 : (count_pre <= 100000)) (PreH3 : (left_pre < middle)) (PreH4 : (middle < right_pre)) (PreH5 : ((Zlength (work_mid_h)) = count_pre)) (PreH6 : ((Zlength (work_mid_i)) = count_pre)) (PreH7 : ((Zlength (work_h)) = count_pre)) (PreH8 : ((Zlength (work_i)) = count_pre)) (PreH9 : ((Zlength (work_h1)) = count_pre)) (PreH10 : ((Zlength (work_i1)) = count_pre)) (PreH11 : ((Zlength (buffer_h)) = count_pre)) (PreH12 : ((Zlength (buffer_i)) = count_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : (left_pre <= k)) (PreH15 : (k <= right_pre)) (PreH16 : (right_pre <= count_pre)) (PreH17 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle )) (PreH18 : (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre )) (PreH19 : (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre )) (PreH20 : (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre k )) ,
  (IntArray.full bufferIndex_pre count_pre buffer_i )
  **  (IntArray.full workHeight_pre count_pre (replace_Znth (k) ((Znth k buffer_h 0)) (work_h1)) )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
  **  (IntArray.full workIndex_pre count_pre work_i1 )
|--
  “ (k < right_pre) ” 
  &&  “ (count_pre <= 100000) ” 
  &&  “ (left_pre < middle) ” 
  &&  “ (middle < right_pre) ” 
  &&  “ ((Zlength (work_mid_h)) = count_pre) ” 
  &&  “ ((Zlength (work_mid_i)) = count_pre) ” 
  &&  “ ((Zlength (work_h)) = count_pre) ” 
  &&  “ ((Zlength (work_i)) = count_pre) ” 
  &&  “ ((Zlength (work_h1)) = count_pre) ” 
  &&  “ ((Zlength (work_i1)) = count_pre) ” 
  &&  “ ((Zlength (buffer_h)) = count_pre) ” 
  &&  “ ((Zlength (buffer_i)) = count_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= k) ” 
  &&  “ (k <= right_pre) ” 
  &&  “ (right_pre <= count_pre) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work0_h work0_i work_mid_h work_mid_i left_pre middle ) ” 
  &&  “ (HeightIndexRangeSortResultNLogN work_mid_h work_mid_i work_h work_i middle right_pre ) ” 
  &&  “ (HeightIndexRangeMergeResultNLogN work_h work_i buffer0_h buffer0_i buffer_h buffer_i left_pre middle right_pre ) ” 
  &&  “ (CopyHeightIndexPrefixNLogN buffer_h buffer_i work_h work_i work_h1 work_i1 left_pre right_pre k ) ”
  &&  (((workIndex_pre + (k * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i workIndex_pre k 0 count_pre work_i1 )
  **  (IntArray.full bufferIndex_pre count_pre buffer_i )
  **  (IntArray.full workHeight_pre count_pre (replace_Znth (k) ((Znth k buffer_h 0)) (work_h1)) )
  **  (IntArray.full bufferHeight_pre count_pre buffer_h )
.

(*----- Function maxAreaNLogN -----*)

Definition maxAreaNLogN_safety_wit_1 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < heightSize_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.undef_full workHeight_pre heightSize_pre )
  **  (IntArray.undef_full workIndex_pre heightSize_pre )
  **  (IntArray.undef_full bufferHeight_pre heightSize_pre )
  **  (IntArray.undef_full bufferIndex_pre heightSize_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxAreaNLogN_safety_wit_2 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_i: (@list Z)) (work_h: (@list Z)) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h)) = k)) (PreH8 : ((Zlength (work_i)) = k)) (PreH9 : ((Zlength (buffer_h)) = k)) (PreH10 : ((Zlength (buffer_i)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h work_i k )) (PreH12 : (WorkspacePrefixNLogN l buffer_h buffer_i k )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  (IntArray.full bufferIndex_pre (k + 1 ) (app (buffer_i) ((cons (k) ((@nil Z))))) )
  **  (IntArray.undef_seg bufferIndex_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full bufferHeight_pre (k + 1 ) (app (buffer_h) ((cons ((Znth k l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg bufferHeight_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full workIndex_pre (k + 1 ) (app (work_i) ((cons (k) ((@nil Z))))) )
  **  (IntArray.undef_seg workIndex_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full workHeight_pre (k + 1 ) (app (work_h) ((cons ((Znth k l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg workHeight_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full height_pre heightSize_pre l )
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_3 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (work0_h: (@list Z)) (work0_i: (@list Z)) (buffer0_h: (@list Z)) (buffer0_i: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : ((Zlength (work0_h)) = heightSize_pre)) (PreH5 : ((Zlength (work0_i)) = heightSize_pre)) (PreH6 : ((Zlength (buffer0_h)) = heightSize_pre)) (PreH7 : ((Zlength (buffer0_i)) = heightSize_pre)) (PreH8 : (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre )) (PreH9 : (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre )) (PreH10 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre work0_h )
  **  (IntArray.full workIndex_pre heightSize_pre work0_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer0_i )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxAreaNLogN_safety_wit_4 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH5 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "minimumIndex" ) )) # Int  |->_)
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxAreaNLogN_safety_wit_5 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH5 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "maximumIndex" ) )) # Int  |->_)
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  ((( &( "minimumIndex" ) )) # Int  |-> (Znth 0 sorted_i 0))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxAreaNLogN_safety_wit_6 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH5 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "maximumArea" ) )) # Int  |->_)
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  ((( &( "maximumIndex" ) )) # Int  |-> (Znth 0 sorted_i 0))
  **  ((( &( "minimumIndex" ) )) # Int  |-> (Znth 0 sorted_i 0))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxAreaNLogN_safety_wit_7 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH5 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "maximumArea" ) )) # Int  |-> 0)
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  ((( &( "maximumIndex" ) )) # Int  |-> (Znth 0 sorted_i 0))
  **  ((( &( "minimumIndex" ) )) # Int  |-> (Znth 0 sorted_i 0))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition maxAreaNLogN_safety_wit_8 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : (0 <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH15 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "distanceToMinimum" ) )) # Int  |->_)
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  ((( &( "currentHeight" ) )) # Int  |-> (Znth k sorted_h 0))
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  ((( &( "index" ) )) # Int  |-> (Znth k sorted_i 0))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ (((Znth k sorted_i 0) - minimumIndex ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth k sorted_i 0) - minimumIndex )) ”
) \/
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : (0 <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH15 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "distanceToMinimum" ) )) # Int  |->_)
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  ((( &( "currentHeight" ) )) # Int  |-> (Znth k sorted_h 0))
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  ((( &( "index" ) )) # Int  |-> (Znth k sorted_i 0))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ (((Znth k sorted_i 0) - minimumIndex ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth k sorted_i 0) - minimumIndex )) ”
).

Definition maxAreaNLogN_safety_wit_8_split_goal_1 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : (0 <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH15 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "distanceToMinimum" ) )) # Int  |->_)
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  ((( &( "currentHeight" ) )) # Int  |-> (Znth k sorted_h 0))
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  ((( &( "index" ) )) # Int  |-> (Znth k sorted_i 0))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ (((Znth k sorted_i 0) - minimumIndex ) <= INT_MAX) ”
.

Definition maxAreaNLogN_safety_wit_8_split_goal_2 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : (0 <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH15 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "distanceToMinimum" ) )) # Int  |->_)
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  ((( &( "currentHeight" ) )) # Int  |-> (Znth k sorted_h 0))
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  ((( &( "index" ) )) # Int  |-> (Znth k sorted_i 0))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((INT_MIN) <= ((Znth k sorted_i 0) - minimumIndex )) ”
.

Definition maxAreaNLogN_safety_wit_9 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : (0 <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH15 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "distanceToMaximum" ) )) # Int  |->_)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> ((Znth k sorted_i 0) - minimumIndex ))
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  ((( &( "currentHeight" ) )) # Int  |-> (Znth k sorted_h 0))
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  ((( &( "index" ) )) # Int  |-> (Znth k sorted_i 0))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((maximumIndex - (Znth k sorted_i 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (maximumIndex - (Znth k sorted_i 0) )) ”
) \/
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : (0 <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH15 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "distanceToMaximum" ) )) # Int  |->_)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> ((Znth k sorted_i 0) - minimumIndex ))
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  ((( &( "currentHeight" ) )) # Int  |-> (Znth k sorted_h 0))
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  ((( &( "index" ) )) # Int  |-> (Znth k sorted_i 0))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((maximumIndex - (Znth k sorted_i 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (maximumIndex - (Znth k sorted_i 0) )) ”
).

Definition maxAreaNLogN_safety_wit_9_split_goal_1 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : (0 <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH15 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "distanceToMaximum" ) )) # Int  |->_)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> ((Znth k sorted_i 0) - minimumIndex ))
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  ((( &( "currentHeight" ) )) # Int  |-> (Znth k sorted_h 0))
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  ((( &( "index" ) )) # Int  |-> (Znth k sorted_i 0))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((maximumIndex - (Znth k sorted_i 0) ) <= INT_MAX) ”
.

Definition maxAreaNLogN_safety_wit_9_split_goal_2 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : (0 <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH15 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "distanceToMaximum" ) )) # Int  |->_)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> ((Znth k sorted_i 0) - minimumIndex ))
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  ((( &( "currentHeight" ) )) # Int  |-> (Znth k sorted_h 0))
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  ((( &( "index" ) )) # Int  |-> (Znth k sorted_i 0))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((INT_MIN) <= (maximumIndex - (Znth k sorted_i 0) )) ”
.

Definition maxAreaNLogN_safety_wit_10 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : (0 <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH15 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "distanceToMaximum" ) )) # Int  |-> (maximumIndex - (Znth k sorted_i 0) ))
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> ((Znth k sorted_i 0) - minimumIndex ))
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  ((( &( "currentHeight" ) )) # Int  |-> (Znth k sorted_h 0))
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  ((( &( "index" ) )) # Int  |-> (Znth k sorted_i 0))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxAreaNLogN_safety_wit_11 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (((Znth k sorted_i 0) - minimumIndex ) < 0)) (PreH2 : (k < heightSize_pre)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k <= heightSize_pre)) (PreH8 : (0 <= minimumIndex)) (PreH9 : (minimumIndex <= maximumIndex)) (PreH10 : (maximumIndex < heightSize_pre)) (PreH11 : (0 <= maximumArea)) (PreH12 : (maximumArea <= 999990000)) (PreH13 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH14 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH15 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH16 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "distanceToMaximum" ) )) # Int  |-> (maximumIndex - (Znth k sorted_i 0) ))
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> ((Znth k sorted_i 0) - minimumIndex ))
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  ((( &( "currentHeight" ) )) # Int  |-> (Znth k sorted_h 0))
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  ((( &( "index" ) )) # Int  |-> (Znth k sorted_i 0))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ (((Znth k sorted_i 0) - minimumIndex ) <> (INT_MIN)) ”
.

Definition maxAreaNLogN_safety_wit_12 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (((Znth k sorted_i 0) - minimumIndex ) < 0)) (PreH2 : (k < heightSize_pre)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k <= heightSize_pre)) (PreH8 : (0 <= minimumIndex)) (PreH9 : (minimumIndex <= maximumIndex)) (PreH10 : (maximumIndex < heightSize_pre)) (PreH11 : (0 <= maximumArea)) (PreH12 : (maximumArea <= 999990000)) (PreH13 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH14 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH15 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH16 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "distanceToMaximum" ) )) # Int  |-> (maximumIndex - (Znth k sorted_i 0) ))
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> (-((Znth k sorted_i 0) - minimumIndex )))
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  ((( &( "currentHeight" ) )) # Int  |-> (Znth k sorted_h 0))
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  ((( &( "index" ) )) # Int  |-> (Znth k sorted_i 0))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxAreaNLogN_safety_wit_13 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (((Znth k sorted_i 0) - minimumIndex ) >= 0)) (PreH2 : (k < heightSize_pre)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k <= heightSize_pre)) (PreH8 : (0 <= minimumIndex)) (PreH9 : (minimumIndex <= maximumIndex)) (PreH10 : (maximumIndex < heightSize_pre)) (PreH11 : (0 <= maximumArea)) (PreH12 : (maximumArea <= 999990000)) (PreH13 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH14 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH15 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH16 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "distanceToMaximum" ) )) # Int  |-> (maximumIndex - (Znth k sorted_i 0) ))
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> ((Znth k sorted_i 0) - minimumIndex ))
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  ((( &( "currentHeight" ) )) # Int  |-> (Znth k sorted_h 0))
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  ((( &( "index" ) )) # Int  |-> (Znth k sorted_i 0))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxAreaNLogN_safety_wit_14 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : ((maximumIndex - (Znth k sorted_i 0) ) < 0)) (PreH2 : (((Znth k sorted_i 0) - minimumIndex ) < 0)) (PreH3 : (k < heightSize_pre)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k <= heightSize_pre)) (PreH9 : (0 <= minimumIndex)) (PreH10 : (minimumIndex <= maximumIndex)) (PreH11 : (maximumIndex < heightSize_pre)) (PreH12 : (0 <= maximumArea)) (PreH13 : (maximumArea <= 999990000)) (PreH14 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH15 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH16 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH17 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "distanceToMaximum" ) )) # Int  |-> (maximumIndex - (Znth k sorted_i 0) ))
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> (-((Znth k sorted_i 0) - minimumIndex )))
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  ((( &( "currentHeight" ) )) # Int  |-> (Znth k sorted_h 0))
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  ((( &( "index" ) )) # Int  |-> (Znth k sorted_i 0))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_15 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : ((maximumIndex - (Znth k sorted_i 0) ) < 0)) (PreH2 : (((Znth k sorted_i 0) - minimumIndex ) >= 0)) (PreH3 : (k < heightSize_pre)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k <= heightSize_pre)) (PreH9 : (0 <= minimumIndex)) (PreH10 : (minimumIndex <= maximumIndex)) (PreH11 : (maximumIndex < heightSize_pre)) (PreH12 : (0 <= maximumArea)) (PreH13 : (maximumArea <= 999990000)) (PreH14 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH15 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH16 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH17 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "distanceToMaximum" ) )) # Int  |-> (maximumIndex - (Znth k sorted_i 0) ))
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> ((Znth k sorted_i 0) - minimumIndex ))
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  ((( &( "currentHeight" ) )) # Int  |-> (Znth k sorted_h 0))
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  ((( &( "index" ) )) # Int  |-> (Znth k sorted_i 0))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((maximumIndex - (Znth k sorted_i 0) ) <> (INT_MIN)) ”
.

Definition maxAreaNLogN_safety_wit_16 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : ((-((Znth k sorted_i 0) - minimumIndex )) > (maximumIndex - (Znth k sorted_i 0) ))) (PreH2 : ((maximumIndex - (Znth k sorted_i 0) ) >= 0)) (PreH3 : (((Znth k sorted_i 0) - minimumIndex ) < 0)) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : (0 <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : (0 <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH18 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "width" ) )) # Int  |->_)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> (maximumIndex - (Znth k sorted_i 0) ))
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> (-((Znth k sorted_i 0) - minimumIndex )))
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  ((( &( "currentHeight" ) )) # Int  |-> (Znth k sorted_h 0))
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  ((( &( "index" ) )) # Int  |-> (Znth k sorted_i 0))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_17 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (1 <= k)) (PreH5 : (k < heightSize_pre)) (PreH6 : (index = (Znth k sorted_i 0))) (PreH7 : (currentHeight = (Znth k sorted_h 0))) (PreH8 : (currentHeight = (Znth index l 0))) (PreH9 : (0 <= index)) (PreH10 : (index < heightSize_pre)) (PreH11 : (0 <= minimumIndex)) (PreH12 : (minimumIndex <= maximumIndex)) (PreH13 : (maximumIndex < heightSize_pre)) (PreH14 : (0 <= currentHeight)) (PreH15 : (currentHeight <= 10000)) (PreH16 : (0 <= distanceToMinimum)) (PreH17 : (distanceToMinimum <= 99999)) (PreH18 : (0 <= distanceToMaximum)) (PreH19 : (distanceToMaximum <= 99999)) (PreH20 : (distanceToMinimum = (index - minimumIndex ))) (PreH21 : (distanceToMaximum = (index - maximumIndex ))) (PreH22 : (distanceToMinimum <= width)) (PreH23 : (distanceToMaximum <= width)) (PreH24 : (width = distanceToMinimum)) (PreH25 : (0 <= width)) (PreH26 : (width <= 99999)) (PreH27 : (0 <= maximumArea)) (PreH28 : (maximumArea <= 999990000)) (PreH29 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH30 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH31 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH32 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |->_)
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((width * currentHeight ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (width * currentHeight )) ”
.

Definition maxAreaNLogN_safety_wit_18 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (1 <= k)) (PreH5 : (k < heightSize_pre)) (PreH6 : (index = (Znth k sorted_i 0))) (PreH7 : (currentHeight = (Znth k sorted_h 0))) (PreH8 : (currentHeight = (Znth index l 0))) (PreH9 : (0 <= index)) (PreH10 : (index < heightSize_pre)) (PreH11 : (0 <= minimumIndex)) (PreH12 : (minimumIndex <= maximumIndex)) (PreH13 : (maximumIndex < heightSize_pre)) (PreH14 : (0 <= currentHeight)) (PreH15 : (currentHeight <= 10000)) (PreH16 : (0 <= distanceToMinimum)) (PreH17 : (distanceToMinimum <= 99999)) (PreH18 : (0 <= distanceToMaximum)) (PreH19 : (distanceToMaximum <= 99999)) (PreH20 : (distanceToMinimum = (index - minimumIndex ))) (PreH21 : (distanceToMaximum = (index - maximumIndex ))) (PreH22 : (distanceToMinimum <= width)) (PreH23 : (distanceToMaximum <= width)) (PreH24 : (width = distanceToMaximum)) (PreH25 : (0 <= width)) (PreH26 : (width <= 99999)) (PreH27 : (0 <= maximumArea)) (PreH28 : (maximumArea <= 999990000)) (PreH29 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH30 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH31 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH32 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |->_)
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((width * currentHeight ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (width * currentHeight )) ”
.

Definition maxAreaNLogN_safety_wit_19 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (1 <= k)) (PreH5 : (k < heightSize_pre)) (PreH6 : (index = (Znth k sorted_i 0))) (PreH7 : (currentHeight = (Znth k sorted_h 0))) (PreH8 : (currentHeight = (Znth index l 0))) (PreH9 : (0 <= index)) (PreH10 : (index < heightSize_pre)) (PreH11 : (0 <= minimumIndex)) (PreH12 : (minimumIndex <= maximumIndex)) (PreH13 : (maximumIndex < heightSize_pre)) (PreH14 : (0 <= currentHeight)) (PreH15 : (currentHeight <= 10000)) (PreH16 : (0 <= distanceToMinimum)) (PreH17 : (distanceToMinimum <= 99999)) (PreH18 : (0 <= distanceToMaximum)) (PreH19 : (distanceToMaximum <= 99999)) (PreH20 : (distanceToMinimum = (index - minimumIndex ))) (PreH21 : (distanceToMaximum = (maximumIndex - index ))) (PreH22 : (distanceToMinimum <= width)) (PreH23 : (distanceToMaximum <= width)) (PreH24 : (width = distanceToMinimum)) (PreH25 : (0 <= width)) (PreH26 : (width <= 99999)) (PreH27 : (0 <= maximumArea)) (PreH28 : (maximumArea <= 999990000)) (PreH29 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH30 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH31 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH32 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |->_)
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((width * currentHeight ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (width * currentHeight )) ”
.

Definition maxAreaNLogN_safety_wit_20 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (1 <= k)) (PreH5 : (k < heightSize_pre)) (PreH6 : (index = (Znth k sorted_i 0))) (PreH7 : (currentHeight = (Znth k sorted_h 0))) (PreH8 : (currentHeight = (Znth index l 0))) (PreH9 : (0 <= index)) (PreH10 : (index < heightSize_pre)) (PreH11 : (0 <= minimumIndex)) (PreH12 : (minimumIndex <= maximumIndex)) (PreH13 : (maximumIndex < heightSize_pre)) (PreH14 : (0 <= currentHeight)) (PreH15 : (currentHeight <= 10000)) (PreH16 : (0 <= distanceToMinimum)) (PreH17 : (distanceToMinimum <= 99999)) (PreH18 : (0 <= distanceToMaximum)) (PreH19 : (distanceToMaximum <= 99999)) (PreH20 : (distanceToMinimum = (index - minimumIndex ))) (PreH21 : (distanceToMaximum = (maximumIndex - index ))) (PreH22 : (distanceToMinimum <= width)) (PreH23 : (distanceToMaximum <= width)) (PreH24 : (width = distanceToMaximum)) (PreH25 : (0 <= width)) (PreH26 : (width <= 99999)) (PreH27 : (0 <= maximumArea)) (PreH28 : (maximumArea <= 999990000)) (PreH29 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH30 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH31 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH32 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |->_)
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((width * currentHeight ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (width * currentHeight )) ”
.

Definition maxAreaNLogN_safety_wit_21 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (1 <= k)) (PreH5 : (k < heightSize_pre)) (PreH6 : (index = (Znth k sorted_i 0))) (PreH7 : (currentHeight = (Znth k sorted_h 0))) (PreH8 : (currentHeight = (Znth index l 0))) (PreH9 : (0 <= index)) (PreH10 : (index < heightSize_pre)) (PreH11 : (0 <= minimumIndex)) (PreH12 : (minimumIndex <= maximumIndex)) (PreH13 : (maximumIndex < heightSize_pre)) (PreH14 : (0 <= currentHeight)) (PreH15 : (currentHeight <= 10000)) (PreH16 : (0 <= distanceToMinimum)) (PreH17 : (distanceToMinimum <= 99999)) (PreH18 : (0 <= distanceToMaximum)) (PreH19 : (distanceToMaximum <= 99999)) (PreH20 : (distanceToMinimum = (minimumIndex - index ))) (PreH21 : (distanceToMaximum = (index - maximumIndex ))) (PreH22 : (distanceToMinimum <= width)) (PreH23 : (distanceToMaximum <= width)) (PreH24 : (width = distanceToMinimum)) (PreH25 : (0 <= width)) (PreH26 : (width <= 99999)) (PreH27 : (0 <= maximumArea)) (PreH28 : (maximumArea <= 999990000)) (PreH29 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH30 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH31 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH32 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |->_)
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((width * currentHeight ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (width * currentHeight )) ”
.

Definition maxAreaNLogN_safety_wit_22 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (1 <= k)) (PreH5 : (k < heightSize_pre)) (PreH6 : (index = (Znth k sorted_i 0))) (PreH7 : (currentHeight = (Znth k sorted_h 0))) (PreH8 : (currentHeight = (Znth index l 0))) (PreH9 : (0 <= index)) (PreH10 : (index < heightSize_pre)) (PreH11 : (0 <= minimumIndex)) (PreH12 : (minimumIndex <= maximumIndex)) (PreH13 : (maximumIndex < heightSize_pre)) (PreH14 : (0 <= currentHeight)) (PreH15 : (currentHeight <= 10000)) (PreH16 : (0 <= distanceToMinimum)) (PreH17 : (distanceToMinimum <= 99999)) (PreH18 : (0 <= distanceToMaximum)) (PreH19 : (distanceToMaximum <= 99999)) (PreH20 : (distanceToMinimum = (minimumIndex - index ))) (PreH21 : (distanceToMaximum = (index - maximumIndex ))) (PreH22 : (distanceToMinimum <= width)) (PreH23 : (distanceToMaximum <= width)) (PreH24 : (width = distanceToMaximum)) (PreH25 : (0 <= width)) (PreH26 : (width <= 99999)) (PreH27 : (0 <= maximumArea)) (PreH28 : (maximumArea <= 999990000)) (PreH29 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH30 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH31 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH32 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |->_)
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((width * currentHeight ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (width * currentHeight )) ”
.

Definition maxAreaNLogN_safety_wit_23 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (1 <= k)) (PreH5 : (k < heightSize_pre)) (PreH6 : (index = (Znth k sorted_i 0))) (PreH7 : (currentHeight = (Znth k sorted_h 0))) (PreH8 : (currentHeight = (Znth index l 0))) (PreH9 : (0 <= index)) (PreH10 : (index < heightSize_pre)) (PreH11 : (0 <= minimumIndex)) (PreH12 : (minimumIndex <= maximumIndex)) (PreH13 : (maximumIndex < heightSize_pre)) (PreH14 : (0 <= currentHeight)) (PreH15 : (currentHeight <= 10000)) (PreH16 : (0 <= distanceToMinimum)) (PreH17 : (distanceToMinimum <= 99999)) (PreH18 : (0 <= distanceToMaximum)) (PreH19 : (distanceToMaximum <= 99999)) (PreH20 : (distanceToMinimum = (minimumIndex - index ))) (PreH21 : (distanceToMaximum = (maximumIndex - index ))) (PreH22 : (distanceToMinimum <= width)) (PreH23 : (distanceToMaximum <= width)) (PreH24 : (width = distanceToMinimum)) (PreH25 : (0 <= width)) (PreH26 : (width <= 99999)) (PreH27 : (0 <= maximumArea)) (PreH28 : (maximumArea <= 999990000)) (PreH29 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH30 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH31 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH32 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |->_)
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((width * currentHeight ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (width * currentHeight )) ”
.

Definition maxAreaNLogN_safety_wit_24 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (1 <= k)) (PreH5 : (k < heightSize_pre)) (PreH6 : (index = (Znth k sorted_i 0))) (PreH7 : (currentHeight = (Znth k sorted_h 0))) (PreH8 : (currentHeight = (Znth index l 0))) (PreH9 : (0 <= index)) (PreH10 : (index < heightSize_pre)) (PreH11 : (0 <= minimumIndex)) (PreH12 : (minimumIndex <= maximumIndex)) (PreH13 : (maximumIndex < heightSize_pre)) (PreH14 : (0 <= currentHeight)) (PreH15 : (currentHeight <= 10000)) (PreH16 : (0 <= distanceToMinimum)) (PreH17 : (distanceToMinimum <= 99999)) (PreH18 : (0 <= distanceToMaximum)) (PreH19 : (distanceToMaximum <= 99999)) (PreH20 : (distanceToMinimum = (minimumIndex - index ))) (PreH21 : (distanceToMaximum = (maximumIndex - index ))) (PreH22 : (distanceToMinimum <= width)) (PreH23 : (distanceToMaximum <= width)) (PreH24 : (width = distanceToMaximum)) (PreH25 : (0 <= width)) (PreH26 : (width <= 99999)) (PreH27 : (0 <= maximumArea)) (PreH28 : (maximumArea <= 999990000)) (PreH29 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH30 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH31 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH32 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |->_)
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((width * currentHeight ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (width * currentHeight )) ”
.

Definition maxAreaNLogN_safety_wit_25 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight ) > maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i 0))) (PreH9 : (currentHeight = (Znth k sorted_h 0))) (PreH10 : (currentHeight = (Znth index l 0))) (PreH11 : (0 <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : (0 <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : (0 <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : (0 <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : (0 <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (index - minimumIndex ))) (PreH23 : (distanceToMaximum = (index - maximumIndex ))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMinimum)) (PreH27 : (0 <= width)) (PreH28 : (width <= 99999)) (PreH29 : (0 <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH34 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_26 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight ) > maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i 0))) (PreH9 : (currentHeight = (Znth k sorted_h 0))) (PreH10 : (currentHeight = (Znth index l 0))) (PreH11 : (0 <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : (0 <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : (0 <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : (0 <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : (0 <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (index - minimumIndex ))) (PreH23 : (distanceToMaximum = (index - maximumIndex ))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMaximum)) (PreH27 : (0 <= width)) (PreH28 : (width <= 99999)) (PreH29 : (0 <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH34 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_27 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight ) > maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i 0))) (PreH9 : (currentHeight = (Znth k sorted_h 0))) (PreH10 : (currentHeight = (Znth index l 0))) (PreH11 : (0 <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : (0 <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : (0 <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : (0 <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : (0 <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (index - minimumIndex ))) (PreH23 : (distanceToMaximum = (maximumIndex - index ))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMinimum)) (PreH27 : (0 <= width)) (PreH28 : (width <= 99999)) (PreH29 : (0 <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH34 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_28 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight ) > maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i 0))) (PreH9 : (currentHeight = (Znth k sorted_h 0))) (PreH10 : (currentHeight = (Znth index l 0))) (PreH11 : (0 <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : (0 <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : (0 <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : (0 <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : (0 <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (index - minimumIndex ))) (PreH23 : (distanceToMaximum = (maximumIndex - index ))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMaximum)) (PreH27 : (0 <= width)) (PreH28 : (width <= 99999)) (PreH29 : (0 <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH34 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_29 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight ) > maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i 0))) (PreH9 : (currentHeight = (Znth k sorted_h 0))) (PreH10 : (currentHeight = (Znth index l 0))) (PreH11 : (0 <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : (0 <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : (0 <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : (0 <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : (0 <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (minimumIndex - index ))) (PreH23 : (distanceToMaximum = (index - maximumIndex ))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMinimum)) (PreH27 : (0 <= width)) (PreH28 : (width <= 99999)) (PreH29 : (0 <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH34 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_30 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight ) > maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i 0))) (PreH9 : (currentHeight = (Znth k sorted_h 0))) (PreH10 : (currentHeight = (Znth index l 0))) (PreH11 : (0 <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : (0 <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : (0 <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : (0 <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : (0 <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (minimumIndex - index ))) (PreH23 : (distanceToMaximum = (index - maximumIndex ))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMaximum)) (PreH27 : (0 <= width)) (PreH28 : (width <= 99999)) (PreH29 : (0 <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH34 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_31 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight ) <= maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i 0))) (PreH9 : (currentHeight = (Znth k sorted_h 0))) (PreH10 : (currentHeight = (Znth index l 0))) (PreH11 : (0 <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : (0 <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : (0 <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : (0 <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : (0 <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (index - minimumIndex ))) (PreH23 : (distanceToMaximum = (index - maximumIndex ))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMinimum)) (PreH27 : (0 <= width)) (PreH28 : (width <= 99999)) (PreH29 : (0 <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH34 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_32 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight ) <= maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i 0))) (PreH9 : (currentHeight = (Znth k sorted_h 0))) (PreH10 : (currentHeight = (Znth index l 0))) (PreH11 : (0 <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : (0 <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : (0 <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : (0 <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : (0 <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (index - minimumIndex ))) (PreH23 : (distanceToMaximum = (index - maximumIndex ))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMaximum)) (PreH27 : (0 <= width)) (PreH28 : (width <= 99999)) (PreH29 : (0 <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH34 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_33 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight ) <= maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i 0))) (PreH9 : (currentHeight = (Znth k sorted_h 0))) (PreH10 : (currentHeight = (Znth index l 0))) (PreH11 : (0 <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : (0 <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : (0 <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : (0 <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : (0 <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (index - minimumIndex ))) (PreH23 : (distanceToMaximum = (maximumIndex - index ))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMinimum)) (PreH27 : (0 <= width)) (PreH28 : (width <= 99999)) (PreH29 : (0 <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH34 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_34 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight ) <= maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i 0))) (PreH9 : (currentHeight = (Znth k sorted_h 0))) (PreH10 : (currentHeight = (Znth index l 0))) (PreH11 : (0 <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : (0 <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : (0 <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : (0 <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : (0 <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (index - minimumIndex ))) (PreH23 : (distanceToMaximum = (maximumIndex - index ))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMaximum)) (PreH27 : (0 <= width)) (PreH28 : (width <= 99999)) (PreH29 : (0 <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH34 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_35 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight ) <= maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i 0))) (PreH9 : (currentHeight = (Znth k sorted_h 0))) (PreH10 : (currentHeight = (Znth index l 0))) (PreH11 : (0 <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : (0 <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : (0 <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : (0 <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : (0 <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (minimumIndex - index ))) (PreH23 : (distanceToMaximum = (index - maximumIndex ))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMinimum)) (PreH27 : (0 <= width)) (PreH28 : (width <= 99999)) (PreH29 : (0 <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH34 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_36 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight ) <= maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i 0))) (PreH9 : (currentHeight = (Znth k sorted_h 0))) (PreH10 : (currentHeight = (Znth index l 0))) (PreH11 : (0 <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : (0 <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : (0 <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : (0 <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : (0 <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (minimumIndex - index ))) (PreH23 : (distanceToMaximum = (index - maximumIndex ))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMaximum)) (PreH27 : (0 <= width)) (PreH28 : (width <= 99999)) (PreH29 : (0 <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH34 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_37 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index > maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight ) <= INT_MAX)) (PreH11 : (distanceToMinimum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight ) >= INT_MIN)) (PreH19 : (index < minimumIndex)) (PreH20 : ((width * currentHeight ) > maximumArea)) (PreH21 : (2 <= heightSize_pre)) (PreH22 : (heightSize_pre <= 100000)) (PreH23 : ((Zlength (l)) = heightSize_pre)) (PreH24 : (1 <= k)) (PreH25 : (k < heightSize_pre)) (PreH26 : (index = (Znth k sorted_i 0))) (PreH27 : (currentHeight = (Znth k sorted_h 0))) (PreH28 : (currentHeight = (Znth index l 0))) (PreH29 : (0 <= index)) (PreH30 : (index < heightSize_pre)) (PreH31 : (0 <= minimumIndex)) (PreH32 : (minimumIndex <= maximumIndex)) (PreH33 : (maximumIndex < heightSize_pre)) (PreH34 : (0 <= currentHeight)) (PreH35 : (currentHeight <= 10000)) (PreH36 : (0 <= distanceToMinimum)) (PreH37 : (distanceToMinimum <= 99999)) (PreH38 : (0 <= distanceToMaximum)) (PreH39 : (distanceToMaximum <= 99999)) (PreH40 : (distanceToMinimum = (minimumIndex - index ))) (PreH41 : (distanceToMaximum = (maximumIndex - index ))) (PreH42 : (distanceToMinimum <= width)) (PreH43 : (distanceToMaximum <= width)) (PreH44 : (width = distanceToMinimum)) (PreH45 : (0 <= width)) (PreH46 : (width <= 99999)) (PreH47 : (0 <= maximumArea)) (PreH48 : (maximumArea <= 999990000)) (PreH49 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH50 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH51 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH52 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> index)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_38 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index > maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight ) <= INT_MAX)) (PreH11 : (distanceToMinimum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight ) >= INT_MIN)) (PreH19 : (index < minimumIndex)) (PreH20 : ((width * currentHeight ) > maximumArea)) (PreH21 : (2 <= heightSize_pre)) (PreH22 : (heightSize_pre <= 100000)) (PreH23 : ((Zlength (l)) = heightSize_pre)) (PreH24 : (1 <= k)) (PreH25 : (k < heightSize_pre)) (PreH26 : (index = (Znth k sorted_i 0))) (PreH27 : (currentHeight = (Znth k sorted_h 0))) (PreH28 : (currentHeight = (Znth index l 0))) (PreH29 : (0 <= index)) (PreH30 : (index < heightSize_pre)) (PreH31 : (0 <= minimumIndex)) (PreH32 : (minimumIndex <= maximumIndex)) (PreH33 : (maximumIndex < heightSize_pre)) (PreH34 : (0 <= currentHeight)) (PreH35 : (currentHeight <= 10000)) (PreH36 : (0 <= distanceToMinimum)) (PreH37 : (distanceToMinimum <= 99999)) (PreH38 : (0 <= distanceToMaximum)) (PreH39 : (distanceToMaximum <= 99999)) (PreH40 : (distanceToMinimum = (minimumIndex - index ))) (PreH41 : (distanceToMaximum = (maximumIndex - index ))) (PreH42 : (distanceToMinimum <= width)) (PreH43 : (distanceToMaximum <= width)) (PreH44 : (width = distanceToMaximum)) (PreH45 : (0 <= width)) (PreH46 : (width <= 99999)) (PreH47 : (0 <= maximumArea)) (PreH48 : (maximumArea <= 999990000)) (PreH49 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH50 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH51 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH52 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> index)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_39 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index > maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (maximumArea <= INT_MAX)) (PreH4 : (distanceToMinimum <= INT_MAX)) (PreH5 : (maximumIndex <= INT_MAX)) (PreH6 : (minimumIndex <= INT_MAX)) (PreH7 : (currentHeight <= INT_MAX)) (PreH8 : (index <= INT_MAX)) (PreH9 : (k <= INT_MAX)) (PreH10 : (heightSize_pre <= INT_MAX)) (PreH11 : ((width * currentHeight ) <= INT_MAX)) (PreH12 : (maximumArea >= INT_MIN)) (PreH13 : (distanceToMinimum >= INT_MIN)) (PreH14 : (maximumIndex >= INT_MIN)) (PreH15 : (minimumIndex >= INT_MIN)) (PreH16 : (currentHeight >= INT_MIN)) (PreH17 : (index >= INT_MIN)) (PreH18 : (k >= INT_MIN)) (PreH19 : (heightSize_pre >= INT_MIN)) (PreH20 : ((width * currentHeight ) >= INT_MIN)) (PreH21 : (index < minimumIndex)) (PreH22 : ((width * currentHeight ) <= maximumArea)) (PreH23 : (2 <= heightSize_pre)) (PreH24 : (heightSize_pre <= 100000)) (PreH25 : ((Zlength (l)) = heightSize_pre)) (PreH26 : (1 <= k)) (PreH27 : (k < heightSize_pre)) (PreH28 : (index = (Znth k sorted_i 0))) (PreH29 : (currentHeight = (Znth k sorted_h 0))) (PreH30 : (currentHeight = (Znth index l 0))) (PreH31 : (0 <= index)) (PreH32 : (index < heightSize_pre)) (PreH33 : (0 <= minimumIndex)) (PreH34 : (minimumIndex <= maximumIndex)) (PreH35 : (maximumIndex < heightSize_pre)) (PreH36 : (0 <= currentHeight)) (PreH37 : (currentHeight <= 10000)) (PreH38 : (0 <= distanceToMinimum)) (PreH39 : (distanceToMinimum <= 99999)) (PreH40 : (0 <= distanceToMaximum)) (PreH41 : (distanceToMaximum <= 99999)) (PreH42 : (distanceToMinimum = (minimumIndex - index ))) (PreH43 : (distanceToMaximum = (maximumIndex - index ))) (PreH44 : (distanceToMinimum <= width)) (PreH45 : (distanceToMaximum <= width)) (PreH46 : (width = distanceToMinimum)) (PreH47 : (0 <= width)) (PreH48 : (width <= 99999)) (PreH49 : (0 <= maximumArea)) (PreH50 : (maximumArea <= 999990000)) (PreH51 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH52 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH53 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH54 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> index)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_40 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index > maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (maximumArea <= INT_MAX)) (PreH4 : (distanceToMinimum <= INT_MAX)) (PreH5 : (maximumIndex <= INT_MAX)) (PreH6 : (minimumIndex <= INT_MAX)) (PreH7 : (currentHeight <= INT_MAX)) (PreH8 : (index <= INT_MAX)) (PreH9 : (k <= INT_MAX)) (PreH10 : (heightSize_pre <= INT_MAX)) (PreH11 : ((width * currentHeight ) <= INT_MAX)) (PreH12 : (maximumArea >= INT_MIN)) (PreH13 : (distanceToMinimum >= INT_MIN)) (PreH14 : (maximumIndex >= INT_MIN)) (PreH15 : (minimumIndex >= INT_MIN)) (PreH16 : (currentHeight >= INT_MIN)) (PreH17 : (index >= INT_MIN)) (PreH18 : (k >= INT_MIN)) (PreH19 : (heightSize_pre >= INT_MIN)) (PreH20 : ((width * currentHeight ) >= INT_MIN)) (PreH21 : (index < minimumIndex)) (PreH22 : ((width * currentHeight ) <= maximumArea)) (PreH23 : (2 <= heightSize_pre)) (PreH24 : (heightSize_pre <= 100000)) (PreH25 : ((Zlength (l)) = heightSize_pre)) (PreH26 : (1 <= k)) (PreH27 : (k < heightSize_pre)) (PreH28 : (index = (Znth k sorted_i 0))) (PreH29 : (currentHeight = (Znth k sorted_h 0))) (PreH30 : (currentHeight = (Znth index l 0))) (PreH31 : (0 <= index)) (PreH32 : (index < heightSize_pre)) (PreH33 : (0 <= minimumIndex)) (PreH34 : (minimumIndex <= maximumIndex)) (PreH35 : (maximumIndex < heightSize_pre)) (PreH36 : (0 <= currentHeight)) (PreH37 : (currentHeight <= 10000)) (PreH38 : (0 <= distanceToMinimum)) (PreH39 : (distanceToMinimum <= 99999)) (PreH40 : (0 <= distanceToMaximum)) (PreH41 : (distanceToMaximum <= 99999)) (PreH42 : (distanceToMinimum = (minimumIndex - index ))) (PreH43 : (distanceToMaximum = (maximumIndex - index ))) (PreH44 : (distanceToMinimum <= width)) (PreH45 : (distanceToMaximum <= width)) (PreH46 : (width = distanceToMaximum)) (PreH47 : (0 <= width)) (PreH48 : (width <= 99999)) (PreH49 : (0 <= maximumArea)) (PreH50 : (maximumArea <= 999990000)) (PreH51 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH52 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH53 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH54 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> index)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_41 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_42 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_43 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_44 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_45 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_46 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_47 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_48 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_49 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_50 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_51 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_52 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ False ”
.

Definition maxAreaNLogN_safety_wit_53 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (distanceToMinimum = distanceToMinimum)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight ) <= INT_MAX)) (PreH10 : (distanceToMaximum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight ) >= INT_MIN)) (PreH18 : (index > maximumIndex)) (PreH19 : (index >= minimumIndex)) (PreH20 : ((width * currentHeight ) > maximumArea)) (PreH21 : (2 <= heightSize_pre)) (PreH22 : (heightSize_pre <= 100000)) (PreH23 : ((Zlength (l)) = heightSize_pre)) (PreH24 : (1 <= k)) (PreH25 : (k < heightSize_pre)) (PreH26 : (index = (Znth k sorted_i 0))) (PreH27 : (currentHeight = (Znth k sorted_h 0))) (PreH28 : (currentHeight = (Znth index l 0))) (PreH29 : (0 <= index)) (PreH30 : (index < heightSize_pre)) (PreH31 : (0 <= minimumIndex)) (PreH32 : (minimumIndex <= maximumIndex)) (PreH33 : (maximumIndex < heightSize_pre)) (PreH34 : (0 <= currentHeight)) (PreH35 : (currentHeight <= 10000)) (PreH36 : (0 <= distanceToMinimum)) (PreH37 : (distanceToMinimum <= 99999)) (PreH38 : (0 <= distanceToMaximum)) (PreH39 : (distanceToMaximum <= 99999)) (PreH40 : (distanceToMinimum = (index - minimumIndex ))) (PreH41 : (distanceToMaximum = (index - maximumIndex ))) (PreH42 : (distanceToMinimum <= width)) (PreH43 : (distanceToMaximum <= width)) (PreH44 : (width = distanceToMinimum)) (PreH45 : (0 <= width)) (PreH46 : (width <= 99999)) (PreH47 : (0 <= maximumArea)) (PreH48 : (maximumArea <= 999990000)) (PreH49 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH50 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH51 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH52 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> index)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_54 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (distanceToMinimum = distanceToMinimum)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight ) <= INT_MAX)) (PreH10 : (distanceToMaximum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight ) >= INT_MIN)) (PreH18 : (index > maximumIndex)) (PreH19 : (index >= minimumIndex)) (PreH20 : ((width * currentHeight ) > maximumArea)) (PreH21 : (2 <= heightSize_pre)) (PreH22 : (heightSize_pre <= 100000)) (PreH23 : ((Zlength (l)) = heightSize_pre)) (PreH24 : (1 <= k)) (PreH25 : (k < heightSize_pre)) (PreH26 : (index = (Znth k sorted_i 0))) (PreH27 : (currentHeight = (Znth k sorted_h 0))) (PreH28 : (currentHeight = (Znth index l 0))) (PreH29 : (0 <= index)) (PreH30 : (index < heightSize_pre)) (PreH31 : (0 <= minimumIndex)) (PreH32 : (minimumIndex <= maximumIndex)) (PreH33 : (maximumIndex < heightSize_pre)) (PreH34 : (0 <= currentHeight)) (PreH35 : (currentHeight <= 10000)) (PreH36 : (0 <= distanceToMinimum)) (PreH37 : (distanceToMinimum <= 99999)) (PreH38 : (0 <= distanceToMaximum)) (PreH39 : (distanceToMaximum <= 99999)) (PreH40 : (distanceToMinimum = (index - minimumIndex ))) (PreH41 : (distanceToMaximum = (index - maximumIndex ))) (PreH42 : (distanceToMinimum <= width)) (PreH43 : (distanceToMaximum <= width)) (PreH44 : (width = distanceToMaximum)) (PreH45 : (0 <= width)) (PreH46 : (width <= 99999)) (PreH47 : (0 <= maximumArea)) (PreH48 : (maximumArea <= 999990000)) (PreH49 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH50 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH51 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH52 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> index)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_55 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (distanceToMinimum = distanceToMinimum)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMaximum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight ) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMaximum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight ) >= INT_MIN)) (PreH20 : (index > maximumIndex)) (PreH21 : (index >= minimumIndex)) (PreH22 : ((width * currentHeight ) <= maximumArea)) (PreH23 : (2 <= heightSize_pre)) (PreH24 : (heightSize_pre <= 100000)) (PreH25 : ((Zlength (l)) = heightSize_pre)) (PreH26 : (1 <= k)) (PreH27 : (k < heightSize_pre)) (PreH28 : (index = (Znth k sorted_i 0))) (PreH29 : (currentHeight = (Znth k sorted_h 0))) (PreH30 : (currentHeight = (Znth index l 0))) (PreH31 : (0 <= index)) (PreH32 : (index < heightSize_pre)) (PreH33 : (0 <= minimumIndex)) (PreH34 : (minimumIndex <= maximumIndex)) (PreH35 : (maximumIndex < heightSize_pre)) (PreH36 : (0 <= currentHeight)) (PreH37 : (currentHeight <= 10000)) (PreH38 : (0 <= distanceToMinimum)) (PreH39 : (distanceToMinimum <= 99999)) (PreH40 : (0 <= distanceToMaximum)) (PreH41 : (distanceToMaximum <= 99999)) (PreH42 : (distanceToMinimum = (index - minimumIndex ))) (PreH43 : (distanceToMaximum = (index - maximumIndex ))) (PreH44 : (distanceToMinimum <= width)) (PreH45 : (distanceToMaximum <= width)) (PreH46 : (width = distanceToMinimum)) (PreH47 : (0 <= width)) (PreH48 : (width <= 99999)) (PreH49 : (0 <= maximumArea)) (PreH50 : (maximumArea <= 999990000)) (PreH51 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH52 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH53 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH54 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> index)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_56 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (distanceToMinimum = distanceToMinimum)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMaximum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight ) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMaximum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight ) >= INT_MIN)) (PreH20 : (index > maximumIndex)) (PreH21 : (index >= minimumIndex)) (PreH22 : ((width * currentHeight ) <= maximumArea)) (PreH23 : (2 <= heightSize_pre)) (PreH24 : (heightSize_pre <= 100000)) (PreH25 : ((Zlength (l)) = heightSize_pre)) (PreH26 : (1 <= k)) (PreH27 : (k < heightSize_pre)) (PreH28 : (index = (Znth k sorted_i 0))) (PreH29 : (currentHeight = (Znth k sorted_h 0))) (PreH30 : (currentHeight = (Znth index l 0))) (PreH31 : (0 <= index)) (PreH32 : (index < heightSize_pre)) (PreH33 : (0 <= minimumIndex)) (PreH34 : (minimumIndex <= maximumIndex)) (PreH35 : (maximumIndex < heightSize_pre)) (PreH36 : (0 <= currentHeight)) (PreH37 : (currentHeight <= 10000)) (PreH38 : (0 <= distanceToMinimum)) (PreH39 : (distanceToMinimum <= 99999)) (PreH40 : (0 <= distanceToMaximum)) (PreH41 : (distanceToMaximum <= 99999)) (PreH42 : (distanceToMinimum = (index - minimumIndex ))) (PreH43 : (distanceToMaximum = (index - maximumIndex ))) (PreH44 : (distanceToMinimum <= width)) (PreH45 : (distanceToMaximum <= width)) (PreH46 : (width = distanceToMaximum)) (PreH47 : (0 <= width)) (PreH48 : (width <= 99999)) (PreH49 : (0 <= maximumArea)) (PreH50 : (maximumArea <= 999990000)) (PreH51 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH52 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH53 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH54 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> index)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_57 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight ) <= INT_MAX)) (PreH11 : (distanceToMinimum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight ) >= INT_MIN)) (PreH19 : (index < minimumIndex)) (PreH20 : ((width * currentHeight ) > maximumArea)) (PreH21 : (2 <= heightSize_pre)) (PreH22 : (heightSize_pre <= 100000)) (PreH23 : ((Zlength (l)) = heightSize_pre)) (PreH24 : (1 <= k)) (PreH25 : (k < heightSize_pre)) (PreH26 : (index = (Znth k sorted_i 0))) (PreH27 : (currentHeight = (Znth k sorted_h 0))) (PreH28 : (currentHeight = (Znth index l 0))) (PreH29 : (0 <= index)) (PreH30 : (index < heightSize_pre)) (PreH31 : (0 <= minimumIndex)) (PreH32 : (minimumIndex <= maximumIndex)) (PreH33 : (maximumIndex < heightSize_pre)) (PreH34 : (0 <= currentHeight)) (PreH35 : (currentHeight <= 10000)) (PreH36 : (0 <= distanceToMinimum)) (PreH37 : (distanceToMinimum <= 99999)) (PreH38 : (0 <= distanceToMaximum)) (PreH39 : (distanceToMaximum <= 99999)) (PreH40 : (distanceToMinimum = (minimumIndex - index ))) (PreH41 : (distanceToMaximum = (maximumIndex - index ))) (PreH42 : (distanceToMinimum <= width)) (PreH43 : (distanceToMaximum <= width)) (PreH44 : (width = distanceToMinimum)) (PreH45 : (0 <= width)) (PreH46 : (width <= 99999)) (PreH47 : (0 <= maximumArea)) (PreH48 : (maximumArea <= 999990000)) (PreH49 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH50 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH51 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH52 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> index)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_58 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight ) <= INT_MAX)) (PreH11 : (distanceToMinimum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight ) >= INT_MIN)) (PreH19 : (index < minimumIndex)) (PreH20 : ((width * currentHeight ) > maximumArea)) (PreH21 : (2 <= heightSize_pre)) (PreH22 : (heightSize_pre <= 100000)) (PreH23 : ((Zlength (l)) = heightSize_pre)) (PreH24 : (1 <= k)) (PreH25 : (k < heightSize_pre)) (PreH26 : (index = (Znth k sorted_i 0))) (PreH27 : (currentHeight = (Znth k sorted_h 0))) (PreH28 : (currentHeight = (Znth index l 0))) (PreH29 : (0 <= index)) (PreH30 : (index < heightSize_pre)) (PreH31 : (0 <= minimumIndex)) (PreH32 : (minimumIndex <= maximumIndex)) (PreH33 : (maximumIndex < heightSize_pre)) (PreH34 : (0 <= currentHeight)) (PreH35 : (currentHeight <= 10000)) (PreH36 : (0 <= distanceToMinimum)) (PreH37 : (distanceToMinimum <= 99999)) (PreH38 : (0 <= distanceToMaximum)) (PreH39 : (distanceToMaximum <= 99999)) (PreH40 : (distanceToMinimum = (minimumIndex - index ))) (PreH41 : (distanceToMaximum = (maximumIndex - index ))) (PreH42 : (distanceToMinimum <= width)) (PreH43 : (distanceToMaximum <= width)) (PreH44 : (width = distanceToMaximum)) (PreH45 : (0 <= width)) (PreH46 : (width <= 99999)) (PreH47 : (0 <= maximumArea)) (PreH48 : (maximumArea <= 999990000)) (PreH49 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH50 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH51 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH52 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> index)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_59 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (maximumArea <= INT_MAX)) (PreH4 : (distanceToMinimum <= INT_MAX)) (PreH5 : (maximumIndex <= INT_MAX)) (PreH6 : (minimumIndex <= INT_MAX)) (PreH7 : (currentHeight <= INT_MAX)) (PreH8 : (index <= INT_MAX)) (PreH9 : (k <= INT_MAX)) (PreH10 : (heightSize_pre <= INT_MAX)) (PreH11 : ((width * currentHeight ) <= INT_MAX)) (PreH12 : (maximumArea >= INT_MIN)) (PreH13 : (distanceToMinimum >= INT_MIN)) (PreH14 : (maximumIndex >= INT_MIN)) (PreH15 : (minimumIndex >= INT_MIN)) (PreH16 : (currentHeight >= INT_MIN)) (PreH17 : (index >= INT_MIN)) (PreH18 : (k >= INT_MIN)) (PreH19 : (heightSize_pre >= INT_MIN)) (PreH20 : ((width * currentHeight ) >= INT_MIN)) (PreH21 : (index < minimumIndex)) (PreH22 : ((width * currentHeight ) <= maximumArea)) (PreH23 : (2 <= heightSize_pre)) (PreH24 : (heightSize_pre <= 100000)) (PreH25 : ((Zlength (l)) = heightSize_pre)) (PreH26 : (1 <= k)) (PreH27 : (k < heightSize_pre)) (PreH28 : (index = (Znth k sorted_i 0))) (PreH29 : (currentHeight = (Znth k sorted_h 0))) (PreH30 : (currentHeight = (Znth index l 0))) (PreH31 : (0 <= index)) (PreH32 : (index < heightSize_pre)) (PreH33 : (0 <= minimumIndex)) (PreH34 : (minimumIndex <= maximumIndex)) (PreH35 : (maximumIndex < heightSize_pre)) (PreH36 : (0 <= currentHeight)) (PreH37 : (currentHeight <= 10000)) (PreH38 : (0 <= distanceToMinimum)) (PreH39 : (distanceToMinimum <= 99999)) (PreH40 : (0 <= distanceToMaximum)) (PreH41 : (distanceToMaximum <= 99999)) (PreH42 : (distanceToMinimum = (minimumIndex - index ))) (PreH43 : (distanceToMaximum = (maximumIndex - index ))) (PreH44 : (distanceToMinimum <= width)) (PreH45 : (distanceToMaximum <= width)) (PreH46 : (width = distanceToMinimum)) (PreH47 : (0 <= width)) (PreH48 : (width <= 99999)) (PreH49 : (0 <= maximumArea)) (PreH50 : (maximumArea <= 999990000)) (PreH51 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH52 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH53 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH54 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> index)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_60 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (maximumArea <= INT_MAX)) (PreH4 : (distanceToMinimum <= INT_MAX)) (PreH5 : (maximumIndex <= INT_MAX)) (PreH6 : (minimumIndex <= INT_MAX)) (PreH7 : (currentHeight <= INT_MAX)) (PreH8 : (index <= INT_MAX)) (PreH9 : (k <= INT_MAX)) (PreH10 : (heightSize_pre <= INT_MAX)) (PreH11 : ((width * currentHeight ) <= INT_MAX)) (PreH12 : (maximumArea >= INT_MIN)) (PreH13 : (distanceToMinimum >= INT_MIN)) (PreH14 : (maximumIndex >= INT_MIN)) (PreH15 : (minimumIndex >= INT_MIN)) (PreH16 : (currentHeight >= INT_MIN)) (PreH17 : (index >= INT_MIN)) (PreH18 : (k >= INT_MIN)) (PreH19 : (heightSize_pre >= INT_MIN)) (PreH20 : ((width * currentHeight ) >= INT_MIN)) (PreH21 : (index < minimumIndex)) (PreH22 : ((width * currentHeight ) <= maximumArea)) (PreH23 : (2 <= heightSize_pre)) (PreH24 : (heightSize_pre <= 100000)) (PreH25 : ((Zlength (l)) = heightSize_pre)) (PreH26 : (1 <= k)) (PreH27 : (k < heightSize_pre)) (PreH28 : (index = (Znth k sorted_i 0))) (PreH29 : (currentHeight = (Znth k sorted_h 0))) (PreH30 : (currentHeight = (Znth index l 0))) (PreH31 : (0 <= index)) (PreH32 : (index < heightSize_pre)) (PreH33 : (0 <= minimumIndex)) (PreH34 : (minimumIndex <= maximumIndex)) (PreH35 : (maximumIndex < heightSize_pre)) (PreH36 : (0 <= currentHeight)) (PreH37 : (currentHeight <= 10000)) (PreH38 : (0 <= distanceToMinimum)) (PreH39 : (distanceToMinimum <= 99999)) (PreH40 : (0 <= distanceToMaximum)) (PreH41 : (distanceToMaximum <= 99999)) (PreH42 : (distanceToMinimum = (minimumIndex - index ))) (PreH43 : (distanceToMaximum = (maximumIndex - index ))) (PreH44 : (distanceToMinimum <= width)) (PreH45 : (distanceToMaximum <= width)) (PreH46 : (width = distanceToMaximum)) (PreH47 : (0 <= width)) (PreH48 : (width <= 99999)) (PreH49 : (0 <= maximumArea)) (PreH50 : (maximumArea <= 999990000)) (PreH51 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH52 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH53 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH54 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> index)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_61 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_62 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_63 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_64 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_65 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_66 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_67 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_68 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_69 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_70 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_71 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_72 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_73 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_74 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_75 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_safety_wit_76 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition maxAreaNLogN_entail_wit_1 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < heightSize_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.undef_full workHeight_pre heightSize_pre )
  **  (IntArray.undef_full workIndex_pre heightSize_pre )
  **  (IntArray.undef_full bufferHeight_pre heightSize_pre )
  **  (IntArray.undef_full bufferIndex_pre heightSize_pre )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (work_i: (@list Z))  (work_h: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= heightSize_pre) ” 
  &&  “ ((Zlength (work_h)) = 0) ” 
  &&  “ ((Zlength (work_i)) = 0) ” 
  &&  “ ((Zlength (buffer_h)) = 0) ” 
  &&  “ ((Zlength (buffer_i)) = 0) ” 
  &&  “ (WorkspacePrefixNLogN l work_h work_i 0 ) ” 
  &&  “ (WorkspacePrefixNLogN l buffer_h buffer_i 0 ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre 0 work_h )
  **  (IntArray.undef_seg workHeight_pre 0 heightSize_pre )
  **  (IntArray.full workIndex_pre 0 work_i )
  **  (IntArray.undef_seg workIndex_pre 0 heightSize_pre )
  **  (IntArray.full bufferHeight_pre 0 buffer_h )
  **  (IntArray.undef_seg bufferHeight_pre 0 heightSize_pre )
  **  (IntArray.full bufferIndex_pre 0 buffer_i )
  **  (IntArray.undef_seg bufferIndex_pre 0 heightSize_pre )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < heightSize_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (WorkspacePrefixNLogN l (@nil Z) (@nil Z) 0 ) ” 
  &&  “ (WorkspacePrefixNLogN l (@nil Z) (@nil Z) 0 ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_1_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < heightSize_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_1_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < heightSize_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (WorkspacePrefixNLogN l (@nil Z) (@nil Z) 0 )
.

Definition maxAreaNLogN_entail_wit_1_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < heightSize_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (WorkspacePrefixNLogN l (@nil Z) (@nil Z) 0 )
.

Definition maxAreaNLogN_entail_wit_1_split_goal_4 := 
forall (heightSize_pre: Z) (l: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < heightSize_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition maxAreaNLogN_entail_wit_1_split_goal_5 := 
forall (heightSize_pre: Z) (l: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < heightSize_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition maxAreaNLogN_entail_wit_1_split_goal_6 := 
forall (heightSize_pre: Z) (l: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < heightSize_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition maxAreaNLogN_entail_wit_1_split_goal_7 := 
forall (heightSize_pre: Z) (l: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < heightSize_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition maxAreaNLogN_entail_wit_2 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (work_i_2: (@list Z)) (work_h_2: (@list Z)) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h_2)) = k)) (PreH8 : ((Zlength (work_i_2)) = k)) (PreH9 : ((Zlength (buffer_h_2)) = k)) (PreH10 : ((Zlength (buffer_i_2)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h_2 work_i_2 k )) (PreH12 : (WorkspacePrefixNLogN l buffer_h_2 buffer_i_2 k )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  (IntArray.full bufferIndex_pre (k + 1 ) (app (buffer_i_2) ((cons (k) ((@nil Z))))) )
  **  (IntArray.undef_seg bufferIndex_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full bufferHeight_pre (k + 1 ) (app (buffer_h_2) ((cons ((Znth k l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg bufferHeight_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full workIndex_pre (k + 1 ) (app (work_i_2) ((cons (k) ((@nil Z))))) )
  **  (IntArray.undef_seg workIndex_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full workHeight_pre (k + 1 ) (app (work_h_2) ((cons ((Znth k l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg workHeight_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full height_pre heightSize_pre l )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (work_i: (@list Z))  (work_h: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ ((Zlength (work_h)) = (k + 1 )) ” 
  &&  “ ((Zlength (work_i)) = (k + 1 )) ” 
  &&  “ ((Zlength (buffer_h)) = (k + 1 )) ” 
  &&  “ ((Zlength (buffer_i)) = (k + 1 )) ” 
  &&  “ (WorkspacePrefixNLogN l work_h work_i (k + 1 ) ) ” 
  &&  “ (WorkspacePrefixNLogN l buffer_h buffer_i (k + 1 ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre (k + 1 ) work_h )
  **  (IntArray.undef_seg workHeight_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full workIndex_pre (k + 1 ) work_i )
  **  (IntArray.undef_seg workIndex_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full bufferHeight_pre (k + 1 ) buffer_h )
  **  (IntArray.undef_seg bufferHeight_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full bufferIndex_pre (k + 1 ) buffer_i )
  **  (IntArray.undef_seg bufferIndex_pre (k + 1 ) heightSize_pre )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (work_i_2: (@list Z)) (work_h_2: (@list Z)) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h_2)) = k)) (PreH8 : ((Zlength (work_i_2)) = k)) (PreH9 : ((Zlength (buffer_h_2)) = k)) (PreH10 : ((Zlength (buffer_i_2)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h_2 work_i_2 k )) (PreH12 : (WorkspacePrefixNLogN l buffer_h_2 buffer_i_2 k )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  TT && emp 
|--
  “ (WorkspacePrefixNLogN l (app (buffer_h_2) ((cons ((Znth k l 0)) ((@nil Z))))) (app (buffer_i_2) ((cons (k) ((@nil Z))))) (k + 1 ) ) ” 
  &&  “ (WorkspacePrefixNLogN l (app (work_h_2) ((cons ((Znth k l 0)) ((@nil Z))))) (app (work_i_2) ((cons (k) ((@nil Z))))) (k + 1 ) ) ” 
  &&  “ ((Zlength ((app (buffer_i_2) ((cons (k) ((@nil Z))))))) = (k + 1 )) ” 
  &&  “ ((Zlength ((app (buffer_h_2) ((cons ((Znth k l 0)) ((@nil Z))))))) = (k + 1 )) ” 
  &&  “ ((Zlength ((app (work_i_2) ((cons (k) ((@nil Z))))))) = (k + 1 )) ” 
  &&  “ ((Zlength ((app (work_h_2) ((cons ((Znth k l 0)) ((@nil Z))))))) = (k + 1 )) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_2_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (work_i_2: (@list Z)) (work_h_2: (@list Z)) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h_2)) = k)) (PreH8 : ((Zlength (work_i_2)) = k)) (PreH9 : ((Zlength (buffer_h_2)) = k)) (PreH10 : ((Zlength (buffer_i_2)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h_2 work_i_2 k )) (PreH12 : (WorkspacePrefixNLogN l buffer_h_2 buffer_i_2 k )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  (WorkspacePrefixNLogN l (app (buffer_h_2) ((cons ((Znth k l 0)) ((@nil Z))))) (app (buffer_i_2) ((cons (k) ((@nil Z))))) (k + 1 ) )
.

Definition maxAreaNLogN_entail_wit_2_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (work_i_2: (@list Z)) (work_h_2: (@list Z)) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h_2)) = k)) (PreH8 : ((Zlength (work_i_2)) = k)) (PreH9 : ((Zlength (buffer_h_2)) = k)) (PreH10 : ((Zlength (buffer_i_2)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h_2 work_i_2 k )) (PreH12 : (WorkspacePrefixNLogN l buffer_h_2 buffer_i_2 k )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  (WorkspacePrefixNLogN l (app (work_h_2) ((cons ((Znth k l 0)) ((@nil Z))))) (app (work_i_2) ((cons (k) ((@nil Z))))) (k + 1 ) )
.

Definition maxAreaNLogN_entail_wit_2_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (work_i_2: (@list Z)) (work_h_2: (@list Z)) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h_2)) = k)) (PreH8 : ((Zlength (work_i_2)) = k)) (PreH9 : ((Zlength (buffer_h_2)) = k)) (PreH10 : ((Zlength (buffer_i_2)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h_2 work_i_2 k )) (PreH12 : (WorkspacePrefixNLogN l buffer_h_2 buffer_i_2 k )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((Zlength ((app (buffer_i_2) ((cons (k) ((@nil Z))))))) = (k + 1 ))
.

Definition maxAreaNLogN_entail_wit_2_split_goal_4 := 
forall (heightSize_pre: Z) (l: (@list Z)) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (work_i_2: (@list Z)) (work_h_2: (@list Z)) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h_2)) = k)) (PreH8 : ((Zlength (work_i_2)) = k)) (PreH9 : ((Zlength (buffer_h_2)) = k)) (PreH10 : ((Zlength (buffer_i_2)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h_2 work_i_2 k )) (PreH12 : (WorkspacePrefixNLogN l buffer_h_2 buffer_i_2 k )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((Zlength ((app (buffer_h_2) ((cons ((Znth k l 0)) ((@nil Z))))))) = (k + 1 ))
.

Definition maxAreaNLogN_entail_wit_2_split_goal_5 := 
forall (heightSize_pre: Z) (l: (@list Z)) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (work_i_2: (@list Z)) (work_h_2: (@list Z)) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h_2)) = k)) (PreH8 : ((Zlength (work_i_2)) = k)) (PreH9 : ((Zlength (buffer_h_2)) = k)) (PreH10 : ((Zlength (buffer_i_2)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h_2 work_i_2 k )) (PreH12 : (WorkspacePrefixNLogN l buffer_h_2 buffer_i_2 k )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((Zlength ((app (work_i_2) ((cons (k) ((@nil Z))))))) = (k + 1 ))
.

Definition maxAreaNLogN_entail_wit_2_split_goal_6 := 
forall (heightSize_pre: Z) (l: (@list Z)) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (work_i_2: (@list Z)) (work_h_2: (@list Z)) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h_2)) = k)) (PreH8 : ((Zlength (work_i_2)) = k)) (PreH9 : ((Zlength (buffer_h_2)) = k)) (PreH10 : ((Zlength (buffer_i_2)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h_2 work_i_2 k )) (PreH12 : (WorkspacePrefixNLogN l buffer_h_2 buffer_i_2 k )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((Zlength ((app (work_h_2) ((cons ((Znth k l 0)) ((@nil Z))))))) = (k + 1 ))
.

Definition maxAreaNLogN_entail_wit_3 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_i: (@list Z)) (work_h: (@list Z)) (k: Z) (PreH1 : (k >= heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h)) = k)) (PreH8 : ((Zlength (work_i)) = k)) (PreH9 : ((Zlength (buffer_h)) = k)) (PreH10 : ((Zlength (buffer_i)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h work_i k )) (PreH12 : (WorkspacePrefixNLogN l buffer_h buffer_i k )) (PreH13 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre k work_h )
  **  (IntArray.undef_seg workHeight_pre k heightSize_pre )
  **  (IntArray.full workIndex_pre k work_i )
  **  (IntArray.undef_seg workIndex_pre k heightSize_pre )
  **  (IntArray.full bufferHeight_pre k buffer_h )
  **  (IntArray.undef_seg bufferHeight_pre k heightSize_pre )
  **  (IntArray.full bufferIndex_pre k buffer_i )
  **  (IntArray.undef_seg bufferIndex_pre k heightSize_pre )
|--
  EX (buffer0_i: (@list Z))  (buffer0_h: (@list Z))  (work0_i: (@list Z))  (work0_h: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ ((Zlength (work0_h)) = heightSize_pre) ” 
  &&  “ ((Zlength (work0_i)) = heightSize_pre) ” 
  &&  “ ((Zlength (buffer0_h)) = heightSize_pre) ” 
  &&  “ ((Zlength (buffer0_i)) = heightSize_pre) ” 
  &&  “ (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre ) ” 
  &&  “ (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre work0_h )
  **  (IntArray.full workIndex_pre heightSize_pre work0_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer0_i )
) \/
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_i: (@list Z)) (work_h: (@list Z)) (k: Z) (PreH1 : (k >= heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h)) = k)) (PreH8 : ((Zlength (work_i)) = k)) (PreH9 : ((Zlength (buffer_h)) = k)) (PreH10 : ((Zlength (buffer_i)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h work_i k )) (PreH12 : (WorkspacePrefixNLogN l buffer_h buffer_i k )) (PreH13 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full workHeight_pre k work_h )
  **  (IntArray.full workIndex_pre k work_i )
  **  (IntArray.full bufferHeight_pre k buffer_h )
  **  (IntArray.full bufferIndex_pre k buffer_i )
|--
  EX (buffer0_i: (@list Z))  (buffer0_h: (@list Z))  (work0_i: (@list Z))  (work0_h: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ ((Zlength (work0_h)) = heightSize_pre) ” 
  &&  “ ((Zlength (work0_i)) = heightSize_pre) ” 
  &&  “ ((Zlength (buffer0_h)) = heightSize_pre) ” 
  &&  “ ((Zlength (buffer0_i)) = heightSize_pre) ” 
  &&  “ (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre ) ” 
  &&  “ (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full workHeight_pre heightSize_pre work0_h )
  **  (IntArray.full workIndex_pre heightSize_pre work0_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer0_i )
).

Definition maxAreaNLogN_entail_wit_4 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (work0_h: (@list Z)) (work0_i: (@list Z)) (buffer0_h: (@list Z)) (buffer0_i: (@list Z)) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (work_h: (@list Z)) (work_i: (@list Z)) (PreH1 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i 0 heightSize_pre )) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((Zlength (work0_h)) = heightSize_pre)) (PreH6 : ((Zlength (work0_i)) = heightSize_pre)) (PreH7 : ((Zlength (buffer0_h)) = heightSize_pre)) (PreH8 : ((Zlength (buffer0_i)) = heightSize_pre)) (PreH9 : (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre )) (PreH10 : (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre )) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full workHeight_pre heightSize_pre work_h )
  **  (IntArray.full workIndex_pre heightSize_pre work_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
  **  (IntArray.full height_pre heightSize_pre l )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (work0_h: (@list Z)) (work0_i: (@list Z)) (buffer0_h: (@list Z)) (buffer0_i: (@list Z)) (work_h: (@list Z)) (work_i: (@list Z)) (PreH1 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i 0 heightSize_pre )) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((Zlength (work0_h)) = heightSize_pre)) (PreH6 : ((Zlength (work0_i)) = heightSize_pre)) (PreH7 : ((Zlength (buffer0_h)) = heightSize_pre)) (PreH8 : ((Zlength (buffer0_i)) = heightSize_pre)) (PreH9 : (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre )) (PreH10 : (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre )) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l work_h work_i ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_4_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (work0_h: (@list Z)) (work0_i: (@list Z)) (buffer0_h: (@list Z)) (buffer0_i: (@list Z)) (work_h: (@list Z)) (work_i: (@list Z)) (PreH1 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i 0 heightSize_pre )) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((Zlength (work0_h)) = heightSize_pre)) (PreH6 : ((Zlength (work0_i)) = heightSize_pre)) (PreH7 : ((Zlength (buffer0_h)) = heightSize_pre)) (PreH8 : ((Zlength (buffer0_i)) = heightSize_pre)) (PreH9 : (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre )) (PreH10 : (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre )) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_4_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (work0_h: (@list Z)) (work0_i: (@list Z)) (buffer0_h: (@list Z)) (buffer0_i: (@list Z)) (work_h: (@list Z)) (work_i: (@list Z)) (PreH1 : (HeightIndexRangeSortResultNLogN work0_h work0_i work_h work_i 0 heightSize_pre )) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : ((Zlength (work0_h)) = heightSize_pre)) (PreH6 : ((Zlength (work0_i)) = heightSize_pre)) (PreH7 : ((Zlength (buffer0_h)) = heightSize_pre)) (PreH8 : ((Zlength (buffer0_i)) = heightSize_pre)) (PreH9 : (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre )) (PreH10 : (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre )) (PreH11 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (SortedHeightIndexWorkspaceNLogN l work_h work_i )
.

Definition maxAreaNLogN_entail_wit_5 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i )) (PreH5 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i_2: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= heightSize_pre) ” 
  &&  “ (0 <= (Znth 0 sorted_i 0)) ” 
  &&  “ ((Znth 0 sorted_i 0) <= (Znth 0 sorted_i 0)) ” 
  &&  “ ((Znth 0 sorted_i 0) < heightSize_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i_2 ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 1 (Znth 0 sorted_i 0) (Znth 0 sorted_i 0) ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 1 0 ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i )) (PreH5 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i 1 0 ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i 1 (Znth 0 sorted_i 0) (Znth 0 sorted_i 0) ) ” 
  &&  “ ((Znth 0 sorted_i 0) < heightSize_pre) ” 
  &&  “ (0 <= (Znth 0 sorted_i 0)) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_5_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i )) (PreH5 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_5_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i )) (PreH5 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i 1 0 )
.

Definition maxAreaNLogN_entail_wit_5_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i )) (PreH5 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i 1 (Znth 0 sorted_i 0) (Znth 0 sorted_i 0) )
.

Definition maxAreaNLogN_entail_wit_5_split_goal_4 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i )) (PreH5 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  ((Znth 0 sorted_i 0) < heightSize_pre)
.

Definition maxAreaNLogN_entail_wit_5_split_goal_5 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i )) (PreH5 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (0 <= (Znth 0 sorted_i 0))
.

Definition maxAreaNLogN_entail_wit_6_1 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (((Znth k sorted_i 0) - minimumIndex ) > (-(maximumIndex - (Znth k sorted_i 0) )))) (PreH2 : ((maximumIndex - (Znth k sorted_i 0) ) < 0)) (PreH3 : (((Znth k sorted_i 0) - minimumIndex ) >= 0)) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : (0 <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : (0 <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h_2: (@list Z))  (sorted_i_2: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ ((Znth k sorted_i 0) = (Znth k sorted_i_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth k sorted_h_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth (Znth k sorted_i 0) l 0)) ” 
  &&  “ (0 <= (Znth k sorted_i 0)) ” 
  &&  “ ((Znth k sorted_i 0) < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (Znth k sorted_h 0)) ” 
  &&  “ ((Znth k sorted_h 0) <= 10000) ” 
  &&  “ (0 <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= 99999) ” 
  &&  “ (0 <= (-(maximumIndex - (Znth k sorted_i 0) ))) ” 
  &&  “ ((-(maximumIndex - (Znth k sorted_i 0) )) <= 99999) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) = ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ ((-(maximumIndex - (Znth k sorted_i 0) )) = ((Znth k sorted_i 0) - maximumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ ((-(maximumIndex - (Znth k sorted_i 0) )) <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) = ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (0 <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (((Znth k sorted_i 0) - minimumIndex ) > (-(maximumIndex - (Znth k sorted_i 0) )))) (PreH2 : ((maximumIndex - (Znth k sorted_i 0) ) < 0)) (PreH3 : (((Znth k sorted_i 0) - minimumIndex ) >= 0)) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : (0 <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : (0 <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= 99999) ” 
  &&  “ ((-(maximumIndex - (Znth k sorted_i 0) )) <= 99999) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= 99999) ” 
  &&  “ ((Znth k sorted_h 0) <= 10000) ” 
  &&  “ (0 <= (Znth k sorted_h 0)) ” 
  &&  “ ((Znth k sorted_i 0) < heightSize_pre) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth (Znth k sorted_i 0) l 0)) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_6_1_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (((Znth k sorted_i 0) - minimumIndex ) > (-(maximumIndex - (Znth k sorted_i 0) )))) (PreH2 : ((maximumIndex - (Znth k sorted_i 0) ) < 0)) (PreH3 : (((Znth k sorted_i 0) - minimumIndex ) >= 0)) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : (0 <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : (0 <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_6_1_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (((Znth k sorted_i 0) - minimumIndex ) > (-(maximumIndex - (Znth k sorted_i 0) )))) (PreH2 : ((maximumIndex - (Znth k sorted_i 0) ) < 0)) (PreH3 : (((Znth k sorted_i 0) - minimumIndex ) >= 0)) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : (0 <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : (0 <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (((Znth k sorted_i 0) - minimumIndex ) <= 99999)
.

Definition maxAreaNLogN_entail_wit_6_1_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (((Znth k sorted_i 0) - minimumIndex ) > (-(maximumIndex - (Znth k sorted_i 0) )))) (PreH2 : ((maximumIndex - (Znth k sorted_i 0) ) < 0)) (PreH3 : (((Znth k sorted_i 0) - minimumIndex ) >= 0)) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : (0 <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : (0 <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  ((-(maximumIndex - (Znth k sorted_i 0) )) <= 99999)
.

Definition maxAreaNLogN_entail_wit_6_1_split_goal_4 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (((Znth k sorted_i 0) - minimumIndex ) > (-(maximumIndex - (Znth k sorted_i 0) )))) (PreH2 : ((maximumIndex - (Znth k sorted_i 0) ) < 0)) (PreH3 : (((Znth k sorted_i 0) - minimumIndex ) >= 0)) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : (0 <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : (0 <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (((Znth k sorted_i 0) - minimumIndex ) <= 99999)
.

Definition maxAreaNLogN_entail_wit_6_1_split_goal_5 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (((Znth k sorted_i 0) - minimumIndex ) > (-(maximumIndex - (Znth k sorted_i 0) )))) (PreH2 : ((maximumIndex - (Znth k sorted_i 0) ) < 0)) (PreH3 : (((Znth k sorted_i 0) - minimumIndex ) >= 0)) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : (0 <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : (0 <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  ((Znth k sorted_h 0) <= 10000)
.

Definition maxAreaNLogN_entail_wit_6_1_split_goal_6 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (((Znth k sorted_i 0) - minimumIndex ) > (-(maximumIndex - (Znth k sorted_i 0) )))) (PreH2 : ((maximumIndex - (Znth k sorted_i 0) ) < 0)) (PreH3 : (((Znth k sorted_i 0) - minimumIndex ) >= 0)) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : (0 <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : (0 <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (0 <= (Znth k sorted_h 0))
.

Definition maxAreaNLogN_entail_wit_6_1_split_goal_7 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (((Znth k sorted_i 0) - minimumIndex ) > (-(maximumIndex - (Znth k sorted_i 0) )))) (PreH2 : ((maximumIndex - (Znth k sorted_i 0) ) < 0)) (PreH3 : (((Znth k sorted_i 0) - minimumIndex ) >= 0)) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : (0 <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : (0 <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  ((Znth k sorted_i 0) < heightSize_pre)
.

Definition maxAreaNLogN_entail_wit_6_1_split_goal_8 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (((Znth k sorted_i 0) - minimumIndex ) > (-(maximumIndex - (Znth k sorted_i 0) )))) (PreH2 : ((maximumIndex - (Znth k sorted_i 0) ) < 0)) (PreH3 : (((Znth k sorted_i 0) - minimumIndex ) >= 0)) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : (0 <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : (0 <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  ((Znth k sorted_h 0) = (Znth (Znth k sorted_i 0) l 0))
.

Definition maxAreaNLogN_entail_wit_6_2 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (((Znth k sorted_i 0) - minimumIndex ) > (maximumIndex - (Znth k sorted_i 0) ))) (PreH2 : ((maximumIndex - (Znth k sorted_i 0) ) >= 0)) (PreH3 : (((Znth k sorted_i 0) - minimumIndex ) >= 0)) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : (0 <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : (0 <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  (EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h_2: (@list Z))  (sorted_i_2: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ ((Znth k sorted_i 0) = (Znth k sorted_i_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth k sorted_h_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth (Znth k sorted_i 0) l 0)) ” 
  &&  “ (0 <= (Znth k sorted_i 0)) ” 
  &&  “ ((Znth k sorted_i 0) < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (Znth k sorted_h 0)) ” 
  &&  “ ((Znth k sorted_h 0) <= 10000) ” 
  &&  “ (0 <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= 99999) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) = ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = ((Znth k sorted_i 0) - maximumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) = ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (0 <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h_2: (@list Z))  (sorted_i_2: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ ((Znth k sorted_i 0) = (Znth k sorted_i_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth k sorted_h_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth (Znth k sorted_i 0) l 0)) ” 
  &&  “ (0 <= (Znth k sorted_i 0)) ” 
  &&  “ ((Znth k sorted_i 0) < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (Znth k sorted_h 0)) ” 
  &&  “ ((Znth k sorted_h 0) <= 10000) ” 
  &&  “ (0 <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= 99999) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) = ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) = ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (0 <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
.

Definition maxAreaNLogN_entail_wit_6_3 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (((Znth k sorted_i 0) - minimumIndex ) <= (-(maximumIndex - (Znth k sorted_i 0) )))) (PreH2 : ((maximumIndex - (Znth k sorted_i 0) ) < 0)) (PreH3 : (((Znth k sorted_i 0) - minimumIndex ) >= 0)) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : (0 <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : (0 <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  (EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h_2: (@list Z))  (sorted_i_2: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ ((Znth k sorted_i 0) = (Znth k sorted_i_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth k sorted_h_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth (Znth k sorted_i 0) l 0)) ” 
  &&  “ (0 <= (Znth k sorted_i 0)) ” 
  &&  “ ((Znth k sorted_i 0) < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (Znth k sorted_h 0)) ” 
  &&  “ ((Znth k sorted_h 0) <= 10000) ” 
  &&  “ (0 <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= 99999) ” 
  &&  “ (0 <= (-(maximumIndex - (Znth k sorted_i 0) ))) ” 
  &&  “ ((-(maximumIndex - (Znth k sorted_i 0) )) <= 99999) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) = ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ ((-(maximumIndex - (Znth k sorted_i 0) )) = ((Znth k sorted_i 0) - maximumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= (-(maximumIndex - (Znth k sorted_i 0) ))) ” 
  &&  “ ((-(maximumIndex - (Znth k sorted_i 0) )) <= (-(maximumIndex - (Znth k sorted_i 0) ))) ” 
  &&  “ ((-(maximumIndex - (Znth k sorted_i 0) )) = ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (0 <= (-(maximumIndex - (Znth k sorted_i 0) ))) ” 
  &&  “ ((-(maximumIndex - (Znth k sorted_i 0) )) <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h_2: (@list Z))  (sorted_i_2: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ ((Znth k sorted_i 0) = (Znth k sorted_i_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth k sorted_h_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth (Znth k sorted_i 0) l 0)) ” 
  &&  “ (0 <= (Znth k sorted_i 0)) ” 
  &&  “ ((Znth k sorted_i 0) < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (Znth k sorted_h 0)) ” 
  &&  “ ((Znth k sorted_h 0) <= 10000) ” 
  &&  “ (0 <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= 99999) ” 
  &&  “ (0 <= (-(maximumIndex - (Znth k sorted_i 0) ))) ” 
  &&  “ ((-(maximumIndex - (Znth k sorted_i 0) )) <= 99999) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) = ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ ((-(maximumIndex - (Znth k sorted_i 0) )) = ((Znth k sorted_i 0) - maximumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= (-(maximumIndex - (Znth k sorted_i 0) ))) ” 
  &&  “ ((-(maximumIndex - (Znth k sorted_i 0) )) <= (-(maximumIndex - (Znth k sorted_i 0) ))) ” 
  &&  “ ((-(maximumIndex - (Znth k sorted_i 0) )) = (-(maximumIndex - (Znth k sorted_i 0) ))) ” 
  &&  “ (0 <= (-(maximumIndex - (Znth k sorted_i 0) ))) ” 
  &&  “ ((-(maximumIndex - (Znth k sorted_i 0) )) <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
.

Definition maxAreaNLogN_entail_wit_6_4 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : ((-((Znth k sorted_i 0) - minimumIndex )) <= (maximumIndex - (Znth k sorted_i 0) ))) (PreH2 : ((maximumIndex - (Znth k sorted_i 0) ) >= 0)) (PreH3 : (((Znth k sorted_i 0) - minimumIndex ) < 0)) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : (0 <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : (0 <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  (EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h_2: (@list Z))  (sorted_i_2: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ ((Znth k sorted_i 0) = (Znth k sorted_i_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth k sorted_h_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth (Znth k sorted_i 0) l 0)) ” 
  &&  “ (0 <= (Znth k sorted_i 0)) ” 
  &&  “ ((Znth k sorted_i 0) < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (Znth k sorted_h 0)) ” 
  &&  “ ((Znth k sorted_h 0) <= 10000) ” 
  &&  “ (0 <= (-((Znth k sorted_i 0) - minimumIndex ))) ” 
  &&  “ ((-((Znth k sorted_i 0) - minimumIndex )) <= 99999) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ ((-((Znth k sorted_i 0) - minimumIndex )) = (minimumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((-((Znth k sorted_i 0) - minimumIndex )) <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = (-((Znth k sorted_i 0) - minimumIndex ))) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h_2: (@list Z))  (sorted_i_2: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ ((Znth k sorted_i 0) = (Znth k sorted_i_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth k sorted_h_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth (Znth k sorted_i 0) l 0)) ” 
  &&  “ (0 <= (Znth k sorted_i 0)) ” 
  &&  “ ((Znth k sorted_i 0) < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (Znth k sorted_h 0)) ” 
  &&  “ ((Znth k sorted_h 0) <= 10000) ” 
  &&  “ (0 <= (-((Znth k sorted_i 0) - minimumIndex ))) ” 
  &&  “ ((-((Znth k sorted_i 0) - minimumIndex )) <= 99999) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ ((-((Znth k sorted_i 0) - minimumIndex )) = (minimumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((-((Znth k sorted_i 0) - minimumIndex )) <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
.

Definition maxAreaNLogN_entail_wit_6_5 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (((Znth k sorted_i 0) - minimumIndex ) <= (maximumIndex - (Znth k sorted_i 0) ))) (PreH2 : ((maximumIndex - (Znth k sorted_i 0) ) >= 0)) (PreH3 : (((Znth k sorted_i 0) - minimumIndex ) >= 0)) (PreH4 : (k < heightSize_pre)) (PreH5 : (2 <= heightSize_pre)) (PreH6 : (heightSize_pre <= 100000)) (PreH7 : ((Zlength (l)) = heightSize_pre)) (PreH8 : (1 <= k)) (PreH9 : (k <= heightSize_pre)) (PreH10 : (0 <= minimumIndex)) (PreH11 : (minimumIndex <= maximumIndex)) (PreH12 : (maximumIndex < heightSize_pre)) (PreH13 : (0 <= maximumArea)) (PreH14 : (maximumArea <= 999990000)) (PreH15 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH16 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH17 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  (EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h_2: (@list Z))  (sorted_i_2: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ ((Znth k sorted_i 0) = (Znth k sorted_i_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth k sorted_h_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth (Znth k sorted_i 0) l 0)) ” 
  &&  “ (0 <= (Znth k sorted_i 0)) ” 
  &&  “ ((Znth k sorted_i 0) < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (Znth k sorted_h 0)) ” 
  &&  “ ((Znth k sorted_h 0) <= 10000) ” 
  &&  “ (0 <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= 99999) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) = ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = ((Znth k sorted_i 0) - maximumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h_2: (@list Z))  (sorted_i_2: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ ((Znth k sorted_i 0) = (Znth k sorted_i_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth k sorted_h_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth (Znth k sorted_i 0) l 0)) ” 
  &&  “ (0 <= (Znth k sorted_i 0)) ” 
  &&  “ ((Znth k sorted_i 0) < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (Znth k sorted_h 0)) ” 
  &&  “ ((Znth k sorted_h 0) <= 10000) ” 
  &&  “ (0 <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= 99999) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) = ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = ((Znth k sorted_i 0) - maximumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h_2: (@list Z))  (sorted_i_2: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ ((Znth k sorted_i 0) = (Znth k sorted_i_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth k sorted_h_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth (Znth k sorted_i 0) l 0)) ” 
  &&  “ (0 <= (Znth k sorted_i 0)) ” 
  &&  “ ((Znth k sorted_i 0) < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (Znth k sorted_h 0)) ” 
  &&  “ ((Znth k sorted_h 0) <= 10000) ” 
  &&  “ (0 <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= 99999) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) = ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h_2: (@list Z))  (sorted_i_2: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ ((Znth k sorted_i 0) = (Znth k sorted_i_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth k sorted_h_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth (Znth k sorted_i 0) l 0)) ” 
  &&  “ (0 <= (Znth k sorted_i 0)) ” 
  &&  “ ((Znth k sorted_i 0) < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (Znth k sorted_h 0)) ” 
  &&  “ ((Znth k sorted_h 0) <= 10000) ” 
  &&  “ (0 <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= 99999) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) = ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h_2: (@list Z))  (sorted_i_2: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ ((Znth k sorted_i 0) = (Znth k sorted_i_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth k sorted_h_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth (Znth k sorted_i 0) l 0)) ” 
  &&  “ (0 <= (Znth k sorted_i 0)) ” 
  &&  “ ((Znth k sorted_i 0) < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (Znth k sorted_h 0)) ” 
  &&  “ ((Znth k sorted_h 0) <= 10000) ” 
  &&  “ (0 <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= 99999) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) = (minimumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = ((Znth k sorted_i 0) - maximumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h_2: (@list Z))  (sorted_i_2: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ ((Znth k sorted_i 0) = (Znth k sorted_i_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth k sorted_h_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth (Znth k sorted_i 0) l 0)) ” 
  &&  “ (0 <= (Znth k sorted_i 0)) ” 
  &&  “ ((Znth k sorted_i 0) < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (Znth k sorted_h 0)) ” 
  &&  “ ((Znth k sorted_h 0) <= 10000) ” 
  &&  “ (0 <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= 99999) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) = (minimumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = ((Znth k sorted_i 0) - maximumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h_2: (@list Z))  (sorted_i_2: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ ((Znth k sorted_i 0) = (Znth k sorted_i_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth k sorted_h_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth (Znth k sorted_i 0) l 0)) ” 
  &&  “ (0 <= (Znth k sorted_i 0)) ” 
  &&  “ ((Znth k sorted_i 0) < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (Znth k sorted_h 0)) ” 
  &&  “ ((Znth k sorted_h 0) <= 10000) ” 
  &&  “ (0 <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= 99999) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) = (minimumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h_2: (@list Z))  (sorted_i_2: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ ((Znth k sorted_i 0) = (Znth k sorted_i_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth k sorted_h_2 0)) ” 
  &&  “ ((Znth k sorted_h 0) = (Znth (Znth k sorted_i 0) l 0)) ” 
  &&  “ (0 <= (Znth k sorted_i 0)) ” 
  &&  “ ((Znth k sorted_i 0) < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (Znth k sorted_h 0)) ” 
  &&  “ ((Znth k sorted_h 0) <= 10000) ” 
  &&  “ (0 <= ((Znth k sorted_i 0) - minimumIndex )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= 99999) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) = (minimumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ (((Znth k sorted_i 0) - minimumIndex ) <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) = (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ (0 <= (maximumIndex - (Znth k sorted_i 0) )) ” 
  &&  “ ((maximumIndex - (Znth k sorted_i 0) ) <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
.

Definition maxAreaNLogN_entail_wit_7_1 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight ) > maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i 0))) (PreH9 : (currentHeight = (Znth k sorted_h 0))) (PreH10 : (currentHeight = (Znth index l 0))) (PreH11 : (0 <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : (0 <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : (0 <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : (0 <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : (0 <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (minimumIndex - index ))) (PreH23 : (distanceToMaximum = (maximumIndex - index ))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMinimum)) (PreH27 : (0 <= width)) (PreH28 : (width <= 99999)) (PreH29 : (0 <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH34 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  (“ (distanceToMaximum = distanceToMaximum) ” 
  &&  “ (distanceToMinimum <= INT_MAX) ” 
  &&  “ (maximumIndex <= INT_MAX) ” 
  &&  “ (minimumIndex <= INT_MAX) ” 
  &&  “ (currentHeight <= INT_MAX) ” 
  &&  “ (index <= INT_MAX) ” 
  &&  “ (k <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width * currentHeight ) <= INT_MAX) ” 
  &&  “ (distanceToMinimum >= INT_MIN) ” 
  &&  “ (maximumIndex >= INT_MIN) ” 
  &&  “ (minimumIndex >= INT_MIN) ” 
  &&  “ (currentHeight >= INT_MIN) ” 
  &&  “ (index >= INT_MIN) ” 
  &&  “ (k >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width * currentHeight ) >= INT_MIN) ” 
  &&  “ (index < minimumIndex) ” 
  &&  “ ((width * currentHeight ) > maximumArea) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ (index = (Znth k sorted_i 0)) ” 
  &&  “ (currentHeight = (Znth k sorted_h 0)) ” 
  &&  “ (currentHeight = (Znth index l 0)) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= currentHeight) ” 
  &&  “ (currentHeight <= 10000) ” 
  &&  “ (0 <= distanceToMinimum) ” 
  &&  “ (distanceToMinimum <= 99999) ” 
  &&  “ (0 <= distanceToMaximum) ” 
  &&  “ (distanceToMaximum <= 99999) ” 
  &&  “ (distanceToMinimum = (minimumIndex - index )) ” 
  &&  “ (distanceToMaximum = (maximumIndex - index )) ” 
  &&  “ (distanceToMinimum <= width) ” 
  &&  “ (distanceToMaximum <= width) ” 
  &&  “ (width = distanceToMinimum) ” 
  &&  “ (0 <= width) ” 
  &&  “ (width <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (EX (k_2: Z)  (index_2: Z)  (currentHeight_2: Z)  (minimumIndex_2: Z)  (maximumIndex_2: Z)  (distanceToMinimum_2: Z)  (distanceToMaximum_2: Z)  (width_2: Z)  (maximumArea_2: Z) ,
  “ (distanceToMaximum_2 = distanceToMaximum_2) ” 
  &&  “ (distanceToMinimum_2 <= INT_MAX) ” 
  &&  “ (maximumIndex_2 <= INT_MAX) ” 
  &&  “ (minimumIndex_2 <= INT_MAX) ” 
  &&  “ (currentHeight_2 <= INT_MAX) ” 
  &&  “ (index_2 <= INT_MAX) ” 
  &&  “ (k_2 <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width_2 * currentHeight_2 ) <= INT_MAX) ” 
  &&  “ (distanceToMinimum_2 >= INT_MIN) ” 
  &&  “ (maximumIndex_2 >= INT_MIN) ” 
  &&  “ (minimumIndex_2 >= INT_MIN) ” 
  &&  “ (currentHeight_2 >= INT_MIN) ” 
  &&  “ (index_2 >= INT_MIN) ” 
  &&  “ (k_2 >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width_2 * currentHeight_2 ) >= INT_MIN) ” 
  &&  “ (index_2 < minimumIndex_2) ” 
  &&  “ ((width_2 * currentHeight_2 ) > maximumArea_2) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k_2) ” 
  &&  “ (k_2 < heightSize_pre) ” 
  &&  “ (index_2 = (Znth k_2 sorted_i 0)) ” 
  &&  “ (currentHeight_2 = (Znth k_2 sorted_h 0)) ” 
  &&  “ (currentHeight_2 = (Znth index_2 l 0)) ” 
  &&  “ (0 <= index_2) ” 
  &&  “ (index_2 < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex_2) ” 
  &&  “ (minimumIndex_2 <= maximumIndex_2) ” 
  &&  “ (maximumIndex_2 < heightSize_pre) ” 
  &&  “ (0 <= currentHeight_2) ” 
  &&  “ (currentHeight_2 <= 10000) ” 
  &&  “ (0 <= distanceToMinimum_2) ” 
  &&  “ (distanceToMinimum_2 <= 99999) ” 
  &&  “ (0 <= distanceToMaximum_2) ” 
  &&  “ (distanceToMaximum_2 <= 99999) ” 
  &&  “ (distanceToMinimum_2 = (minimumIndex_2 - index_2 )) ” 
  &&  “ (distanceToMaximum_2 = (maximumIndex_2 - index_2 )) ” 
  &&  “ (distanceToMinimum_2 <= width_2) ” 
  &&  “ (distanceToMaximum_2 <= width_2) ” 
  &&  “ (width_2 = distanceToMaximum_2) ” 
  &&  “ (0 <= width_2) ” 
  &&  “ (width_2 <= 99999) ” 
  &&  “ (0 <= maximumArea_2) ” 
  &&  “ (maximumArea_2 <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2 ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2 ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "width" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "area" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k_2)
  **  ((( &( "index" ) )) # Int  |-> index_2)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight_2)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex_2)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex_2)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (EX (k_2: Z)  (index_2: Z)  (currentHeight_2: Z)  (minimumIndex_2: Z)  (maximumIndex_2: Z)  (distanceToMinimum_2: Z)  (distanceToMaximum_2: Z)  (width_2: Z)  (maximumArea_2: Z) ,
  “ (distanceToMaximum_2 = distanceToMaximum_2) ” 
  &&  “ (maximumArea_2 <= INT_MAX) ” 
  &&  “ (distanceToMinimum_2 <= INT_MAX) ” 
  &&  “ (maximumIndex_2 <= INT_MAX) ” 
  &&  “ (minimumIndex_2 <= INT_MAX) ” 
  &&  “ (currentHeight_2 <= INT_MAX) ” 
  &&  “ (index_2 <= INT_MAX) ” 
  &&  “ (k_2 <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width_2 * currentHeight_2 ) <= INT_MAX) ” 
  &&  “ (maximumArea_2 >= INT_MIN) ” 
  &&  “ (distanceToMinimum_2 >= INT_MIN) ” 
  &&  “ (maximumIndex_2 >= INT_MIN) ” 
  &&  “ (minimumIndex_2 >= INT_MIN) ” 
  &&  “ (currentHeight_2 >= INT_MIN) ” 
  &&  “ (index_2 >= INT_MIN) ” 
  &&  “ (k_2 >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width_2 * currentHeight_2 ) >= INT_MIN) ” 
  &&  “ (index_2 < minimumIndex_2) ” 
  &&  “ ((width_2 * currentHeight_2 ) <= maximumArea_2) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k_2) ” 
  &&  “ (k_2 < heightSize_pre) ” 
  &&  “ (index_2 = (Znth k_2 sorted_i 0)) ” 
  &&  “ (currentHeight_2 = (Znth k_2 sorted_h 0)) ” 
  &&  “ (currentHeight_2 = (Znth index_2 l 0)) ” 
  &&  “ (0 <= index_2) ” 
  &&  “ (index_2 < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex_2) ” 
  &&  “ (minimumIndex_2 <= maximumIndex_2) ” 
  &&  “ (maximumIndex_2 < heightSize_pre) ” 
  &&  “ (0 <= currentHeight_2) ” 
  &&  “ (currentHeight_2 <= 10000) ” 
  &&  “ (0 <= distanceToMinimum_2) ” 
  &&  “ (distanceToMinimum_2 <= 99999) ” 
  &&  “ (0 <= distanceToMaximum_2) ” 
  &&  “ (distanceToMaximum_2 <= 99999) ” 
  &&  “ (distanceToMinimum_2 = (minimumIndex_2 - index_2 )) ” 
  &&  “ (distanceToMaximum_2 = (maximumIndex_2 - index_2 )) ” 
  &&  “ (distanceToMinimum_2 <= width_2) ” 
  &&  “ (distanceToMaximum_2 <= width_2) ” 
  &&  “ (width_2 = distanceToMaximum_2) ” 
  &&  “ (0 <= width_2) ” 
  &&  “ (width_2 <= 99999) ” 
  &&  “ (0 <= maximumArea_2) ” 
  &&  “ (maximumArea_2 <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2 ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2 ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "width" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "area" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k_2)
  **  ((( &( "index" ) )) # Int  |-> index_2)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight_2)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex_2)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex_2)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea_2)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
.

Definition maxAreaNLogN_entail_wit_7_2 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k_2: Z) (index_2: Z) (currentHeight_2: Z) (minimumIndex_2: Z) (maximumIndex_2: Z) (distanceToMinimum_2: Z) (distanceToMaximum_2: Z) (width_2: Z) (maximumArea_2: Z) (PreH1 : (index_2 < minimumIndex_2)) (PreH2 : ((width_2 * currentHeight_2 ) > maximumArea_2)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k_2)) (PreH7 : (k_2 < heightSize_pre)) (PreH8 : (index_2 = (Znth k_2 sorted_i 0))) (PreH9 : (currentHeight_2 = (Znth k_2 sorted_h 0))) (PreH10 : (currentHeight_2 = (Znth index_2 l 0))) (PreH11 : (0 <= index_2)) (PreH12 : (index_2 < heightSize_pre)) (PreH13 : (0 <= minimumIndex_2)) (PreH14 : (minimumIndex_2 <= maximumIndex_2)) (PreH15 : (maximumIndex_2 < heightSize_pre)) (PreH16 : (0 <= currentHeight_2)) (PreH17 : (currentHeight_2 <= 10000)) (PreH18 : (0 <= distanceToMinimum_2)) (PreH19 : (distanceToMinimum_2 <= 99999)) (PreH20 : (0 <= distanceToMaximum_2)) (PreH21 : (distanceToMaximum_2 <= 99999)) (PreH22 : (distanceToMinimum_2 = (minimumIndex_2 - index_2 ))) (PreH23 : (distanceToMaximum_2 = (maximumIndex_2 - index_2 ))) (PreH24 : (distanceToMinimum_2 <= width_2)) (PreH25 : (distanceToMaximum_2 <= width_2)) (PreH26 : (width_2 = distanceToMaximum_2)) (PreH27 : (0 <= width_2)) (PreH28 : (width_2 <= 99999)) (PreH29 : (0 <= maximumArea_2)) (PreH30 : (maximumArea_2 <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2 )) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2 )) (PreH34 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k_2)
  **  ((( &( "index" ) )) # Int  |-> index_2)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight_2)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex_2)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex_2)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "width" ) )) # Int  |-> width_2)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  (EX (k: Z)  (index: Z)  (currentHeight: Z)  (minimumIndex: Z)  (maximumIndex: Z)  (distanceToMinimum: Z)  (distanceToMaximum: Z)  (width: Z)  (maximumArea: Z) ,
  “ (distanceToMaximum = distanceToMaximum) ” 
  &&  “ (distanceToMinimum <= INT_MAX) ” 
  &&  “ (maximumIndex <= INT_MAX) ” 
  &&  “ (minimumIndex <= INT_MAX) ” 
  &&  “ (currentHeight <= INT_MAX) ” 
  &&  “ (index <= INT_MAX) ” 
  &&  “ (k <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width * currentHeight ) <= INT_MAX) ” 
  &&  “ (distanceToMinimum >= INT_MIN) ” 
  &&  “ (maximumIndex >= INT_MIN) ” 
  &&  “ (minimumIndex >= INT_MIN) ” 
  &&  “ (currentHeight >= INT_MIN) ” 
  &&  “ (index >= INT_MIN) ” 
  &&  “ (k >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width * currentHeight ) >= INT_MIN) ” 
  &&  “ (index < minimumIndex) ” 
  &&  “ ((width * currentHeight ) > maximumArea) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ (index = (Znth k sorted_i 0)) ” 
  &&  “ (currentHeight = (Znth k sorted_h 0)) ” 
  &&  “ (currentHeight = (Znth index l 0)) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= currentHeight) ” 
  &&  “ (currentHeight <= 10000) ” 
  &&  “ (0 <= distanceToMinimum) ” 
  &&  “ (distanceToMinimum <= 99999) ” 
  &&  “ (0 <= distanceToMaximum) ” 
  &&  “ (distanceToMaximum <= 99999) ” 
  &&  “ (distanceToMinimum = (minimumIndex - index )) ” 
  &&  “ (distanceToMaximum = (maximumIndex - index )) ” 
  &&  “ (distanceToMinimum <= width) ” 
  &&  “ (distanceToMaximum <= width) ” 
  &&  “ (width = distanceToMinimum) ” 
  &&  “ (0 <= width) ” 
  &&  “ (width <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (“ (distanceToMaximum_2 = distanceToMaximum_2) ” 
  &&  “ (distanceToMinimum_2 <= INT_MAX) ” 
  &&  “ (maximumIndex_2 <= INT_MAX) ” 
  &&  “ (minimumIndex_2 <= INT_MAX) ” 
  &&  “ (currentHeight_2 <= INT_MAX) ” 
  &&  “ (index_2 <= INT_MAX) ” 
  &&  “ (k_2 <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width_2 * currentHeight_2 ) <= INT_MAX) ” 
  &&  “ (distanceToMinimum_2 >= INT_MIN) ” 
  &&  “ (maximumIndex_2 >= INT_MIN) ” 
  &&  “ (minimumIndex_2 >= INT_MIN) ” 
  &&  “ (currentHeight_2 >= INT_MIN) ” 
  &&  “ (index_2 >= INT_MIN) ” 
  &&  “ (k_2 >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width_2 * currentHeight_2 ) >= INT_MIN) ” 
  &&  “ (index_2 < minimumIndex_2) ” 
  &&  “ ((width_2 * currentHeight_2 ) > maximumArea_2) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k_2) ” 
  &&  “ (k_2 < heightSize_pre) ” 
  &&  “ (index_2 = (Znth k_2 sorted_i 0)) ” 
  &&  “ (currentHeight_2 = (Znth k_2 sorted_h 0)) ” 
  &&  “ (currentHeight_2 = (Znth index_2 l 0)) ” 
  &&  “ (0 <= index_2) ” 
  &&  “ (index_2 < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex_2) ” 
  &&  “ (minimumIndex_2 <= maximumIndex_2) ” 
  &&  “ (maximumIndex_2 < heightSize_pre) ” 
  &&  “ (0 <= currentHeight_2) ” 
  &&  “ (currentHeight_2 <= 10000) ” 
  &&  “ (0 <= distanceToMinimum_2) ” 
  &&  “ (distanceToMinimum_2 <= 99999) ” 
  &&  “ (0 <= distanceToMaximum_2) ” 
  &&  “ (distanceToMaximum_2 <= 99999) ” 
  &&  “ (distanceToMinimum_2 = (minimumIndex_2 - index_2 )) ” 
  &&  “ (distanceToMaximum_2 = (maximumIndex_2 - index_2 )) ” 
  &&  “ (distanceToMinimum_2 <= width_2) ” 
  &&  “ (distanceToMaximum_2 <= width_2) ” 
  &&  “ (width_2 = distanceToMaximum_2) ” 
  &&  “ (0 <= width_2) ” 
  &&  “ (width_2 <= 99999) ” 
  &&  “ (0 <= maximumArea_2) ” 
  &&  “ (maximumArea_2 <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2 ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2 ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "width" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "area" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k_2)
  **  ((( &( "index" ) )) # Int  |-> index_2)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight_2)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex_2)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex_2)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (EX (k: Z)  (index: Z)  (currentHeight: Z)  (minimumIndex: Z)  (maximumIndex: Z)  (distanceToMinimum: Z)  (distanceToMaximum: Z)  (width: Z)  (maximumArea: Z) ,
  “ (distanceToMaximum = distanceToMaximum) ” 
  &&  “ (maximumArea <= INT_MAX) ” 
  &&  “ (distanceToMinimum <= INT_MAX) ” 
  &&  “ (maximumIndex <= INT_MAX) ” 
  &&  “ (minimumIndex <= INT_MAX) ” 
  &&  “ (currentHeight <= INT_MAX) ” 
  &&  “ (index <= INT_MAX) ” 
  &&  “ (k <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width * currentHeight ) <= INT_MAX) ” 
  &&  “ (maximumArea >= INT_MIN) ” 
  &&  “ (distanceToMinimum >= INT_MIN) ” 
  &&  “ (maximumIndex >= INT_MIN) ” 
  &&  “ (minimumIndex >= INT_MIN) ” 
  &&  “ (currentHeight >= INT_MIN) ” 
  &&  “ (index >= INT_MIN) ” 
  &&  “ (k >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width * currentHeight ) >= INT_MIN) ” 
  &&  “ (index < minimumIndex) ” 
  &&  “ ((width * currentHeight ) <= maximumArea) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ (index = (Znth k sorted_i 0)) ” 
  &&  “ (currentHeight = (Znth k sorted_h 0)) ” 
  &&  “ (currentHeight = (Znth index l 0)) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= currentHeight) ” 
  &&  “ (currentHeight <= 10000) ” 
  &&  “ (0 <= distanceToMinimum) ” 
  &&  “ (distanceToMinimum <= 99999) ” 
  &&  “ (0 <= distanceToMaximum) ” 
  &&  “ (distanceToMaximum <= 99999) ” 
  &&  “ (distanceToMinimum = (minimumIndex - index )) ” 
  &&  “ (distanceToMaximum = (maximumIndex - index )) ” 
  &&  “ (distanceToMinimum <= width) ” 
  &&  “ (distanceToMaximum <= width) ” 
  &&  “ (width = distanceToMinimum) ” 
  &&  “ (0 <= width) ” 
  &&  “ (width <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
.

Definition maxAreaNLogN_entail_wit_7_3 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index < minimumIndex)) (PreH2 : ((width * currentHeight ) <= maximumArea)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k)) (PreH7 : (k < heightSize_pre)) (PreH8 : (index = (Znth k sorted_i 0))) (PreH9 : (currentHeight = (Znth k sorted_h 0))) (PreH10 : (currentHeight = (Znth index l 0))) (PreH11 : (0 <= index)) (PreH12 : (index < heightSize_pre)) (PreH13 : (0 <= minimumIndex)) (PreH14 : (minimumIndex <= maximumIndex)) (PreH15 : (maximumIndex < heightSize_pre)) (PreH16 : (0 <= currentHeight)) (PreH17 : (currentHeight <= 10000)) (PreH18 : (0 <= distanceToMinimum)) (PreH19 : (distanceToMinimum <= 99999)) (PreH20 : (0 <= distanceToMaximum)) (PreH21 : (distanceToMaximum <= 99999)) (PreH22 : (distanceToMinimum = (minimumIndex - index ))) (PreH23 : (distanceToMaximum = (maximumIndex - index ))) (PreH24 : (distanceToMinimum <= width)) (PreH25 : (distanceToMaximum <= width)) (PreH26 : (width = distanceToMinimum)) (PreH27 : (0 <= width)) (PreH28 : (width <= 99999)) (PreH29 : (0 <= maximumArea)) (PreH30 : (maximumArea <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH34 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  (EX (k_2: Z)  (index_2: Z)  (currentHeight_2: Z)  (minimumIndex_2: Z)  (maximumIndex_2: Z)  (distanceToMinimum_2: Z)  (distanceToMaximum_2: Z)  (width_2: Z)  (maximumArea_2: Z) ,
  “ (distanceToMaximum_2 = distanceToMaximum_2) ” 
  &&  “ (distanceToMinimum_2 <= INT_MAX) ” 
  &&  “ (maximumIndex_2 <= INT_MAX) ” 
  &&  “ (minimumIndex_2 <= INT_MAX) ” 
  &&  “ (currentHeight_2 <= INT_MAX) ” 
  &&  “ (index_2 <= INT_MAX) ” 
  &&  “ (k_2 <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width_2 * currentHeight_2 ) <= INT_MAX) ” 
  &&  “ (distanceToMinimum_2 >= INT_MIN) ” 
  &&  “ (maximumIndex_2 >= INT_MIN) ” 
  &&  “ (minimumIndex_2 >= INT_MIN) ” 
  &&  “ (currentHeight_2 >= INT_MIN) ” 
  &&  “ (index_2 >= INT_MIN) ” 
  &&  “ (k_2 >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width_2 * currentHeight_2 ) >= INT_MIN) ” 
  &&  “ (index_2 < minimumIndex_2) ” 
  &&  “ ((width_2 * currentHeight_2 ) > maximumArea_2) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k_2) ” 
  &&  “ (k_2 < heightSize_pre) ” 
  &&  “ (index_2 = (Znth k_2 sorted_i 0)) ” 
  &&  “ (currentHeight_2 = (Znth k_2 sorted_h 0)) ” 
  &&  “ (currentHeight_2 = (Znth index_2 l 0)) ” 
  &&  “ (0 <= index_2) ” 
  &&  “ (index_2 < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex_2) ” 
  &&  “ (minimumIndex_2 <= maximumIndex_2) ” 
  &&  “ (maximumIndex_2 < heightSize_pre) ” 
  &&  “ (0 <= currentHeight_2) ” 
  &&  “ (currentHeight_2 <= 10000) ” 
  &&  “ (0 <= distanceToMinimum_2) ” 
  &&  “ (distanceToMinimum_2 <= 99999) ” 
  &&  “ (0 <= distanceToMaximum_2) ” 
  &&  “ (distanceToMaximum_2 <= 99999) ” 
  &&  “ (distanceToMinimum_2 = (minimumIndex_2 - index_2 )) ” 
  &&  “ (distanceToMaximum_2 = (maximumIndex_2 - index_2 )) ” 
  &&  “ (distanceToMinimum_2 <= width_2) ” 
  &&  “ (distanceToMaximum_2 <= width_2) ” 
  &&  “ (width_2 = distanceToMaximum_2) ” 
  &&  “ (0 <= width_2) ” 
  &&  “ (width_2 <= 99999) ” 
  &&  “ (0 <= maximumArea_2) ” 
  &&  “ (maximumArea_2 <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2 ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2 ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "width" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "area" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k_2)
  **  ((( &( "index" ) )) # Int  |-> index_2)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight_2)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex_2)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex_2)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (“ (distanceToMaximum = distanceToMaximum) ” 
  &&  “ (maximumArea <= INT_MAX) ” 
  &&  “ (distanceToMinimum <= INT_MAX) ” 
  &&  “ (maximumIndex <= INT_MAX) ” 
  &&  “ (minimumIndex <= INT_MAX) ” 
  &&  “ (currentHeight <= INT_MAX) ” 
  &&  “ (index <= INT_MAX) ” 
  &&  “ (k <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width * currentHeight ) <= INT_MAX) ” 
  &&  “ (maximumArea >= INT_MIN) ” 
  &&  “ (distanceToMinimum >= INT_MIN) ” 
  &&  “ (maximumIndex >= INT_MIN) ” 
  &&  “ (minimumIndex >= INT_MIN) ” 
  &&  “ (currentHeight >= INT_MIN) ” 
  &&  “ (index >= INT_MIN) ” 
  &&  “ (k >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width * currentHeight ) >= INT_MIN) ” 
  &&  “ (index < minimumIndex) ” 
  &&  “ ((width * currentHeight ) <= maximumArea) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ (index = (Znth k sorted_i 0)) ” 
  &&  “ (currentHeight = (Znth k sorted_h 0)) ” 
  &&  “ (currentHeight = (Znth index l 0)) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= currentHeight) ” 
  &&  “ (currentHeight <= 10000) ” 
  &&  “ (0 <= distanceToMinimum) ” 
  &&  “ (distanceToMinimum <= 99999) ” 
  &&  “ (0 <= distanceToMaximum) ” 
  &&  “ (distanceToMaximum <= 99999) ” 
  &&  “ (distanceToMinimum = (minimumIndex - index )) ” 
  &&  “ (distanceToMaximum = (maximumIndex - index )) ” 
  &&  “ (distanceToMinimum <= width) ” 
  &&  “ (distanceToMaximum <= width) ” 
  &&  “ (width = distanceToMinimum) ” 
  &&  “ (0 <= width) ” 
  &&  “ (width <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (EX (k_2: Z)  (index_2: Z)  (currentHeight_2: Z)  (minimumIndex_2: Z)  (maximumIndex_2: Z)  (distanceToMinimum_2: Z)  (distanceToMaximum_2: Z)  (width_2: Z)  (maximumArea_2: Z) ,
  “ (distanceToMaximum_2 = distanceToMaximum_2) ” 
  &&  “ (maximumArea_2 <= INT_MAX) ” 
  &&  “ (distanceToMinimum_2 <= INT_MAX) ” 
  &&  “ (maximumIndex_2 <= INT_MAX) ” 
  &&  “ (minimumIndex_2 <= INT_MAX) ” 
  &&  “ (currentHeight_2 <= INT_MAX) ” 
  &&  “ (index_2 <= INT_MAX) ” 
  &&  “ (k_2 <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width_2 * currentHeight_2 ) <= INT_MAX) ” 
  &&  “ (maximumArea_2 >= INT_MIN) ” 
  &&  “ (distanceToMinimum_2 >= INT_MIN) ” 
  &&  “ (maximumIndex_2 >= INT_MIN) ” 
  &&  “ (minimumIndex_2 >= INT_MIN) ” 
  &&  “ (currentHeight_2 >= INT_MIN) ” 
  &&  “ (index_2 >= INT_MIN) ” 
  &&  “ (k_2 >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width_2 * currentHeight_2 ) >= INT_MIN) ” 
  &&  “ (index_2 < minimumIndex_2) ” 
  &&  “ ((width_2 * currentHeight_2 ) <= maximumArea_2) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k_2) ” 
  &&  “ (k_2 < heightSize_pre) ” 
  &&  “ (index_2 = (Znth k_2 sorted_i 0)) ” 
  &&  “ (currentHeight_2 = (Znth k_2 sorted_h 0)) ” 
  &&  “ (currentHeight_2 = (Znth index_2 l 0)) ” 
  &&  “ (0 <= index_2) ” 
  &&  “ (index_2 < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex_2) ” 
  &&  “ (minimumIndex_2 <= maximumIndex_2) ” 
  &&  “ (maximumIndex_2 < heightSize_pre) ” 
  &&  “ (0 <= currentHeight_2) ” 
  &&  “ (currentHeight_2 <= 10000) ” 
  &&  “ (0 <= distanceToMinimum_2) ” 
  &&  “ (distanceToMinimum_2 <= 99999) ” 
  &&  “ (0 <= distanceToMaximum_2) ” 
  &&  “ (distanceToMaximum_2 <= 99999) ” 
  &&  “ (distanceToMinimum_2 = (minimumIndex_2 - index_2 )) ” 
  &&  “ (distanceToMaximum_2 = (maximumIndex_2 - index_2 )) ” 
  &&  “ (distanceToMinimum_2 <= width_2) ” 
  &&  “ (distanceToMaximum_2 <= width_2) ” 
  &&  “ (width_2 = distanceToMaximum_2) ” 
  &&  “ (0 <= width_2) ” 
  &&  “ (width_2 <= 99999) ” 
  &&  “ (0 <= maximumArea_2) ” 
  &&  “ (maximumArea_2 <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2 ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2 ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "width" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "area" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k_2)
  **  ((( &( "index" ) )) # Int  |-> index_2)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight_2)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex_2)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex_2)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea_2)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
.

Definition maxAreaNLogN_entail_wit_7_4 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k_2: Z) (index_2: Z) (currentHeight_2: Z) (minimumIndex_2: Z) (maximumIndex_2: Z) (distanceToMinimum_2: Z) (distanceToMaximum_2: Z) (width_2: Z) (maximumArea_2: Z) (PreH1 : (index_2 < minimumIndex_2)) (PreH2 : ((width_2 * currentHeight_2 ) <= maximumArea_2)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (1 <= k_2)) (PreH7 : (k_2 < heightSize_pre)) (PreH8 : (index_2 = (Znth k_2 sorted_i 0))) (PreH9 : (currentHeight_2 = (Znth k_2 sorted_h 0))) (PreH10 : (currentHeight_2 = (Znth index_2 l 0))) (PreH11 : (0 <= index_2)) (PreH12 : (index_2 < heightSize_pre)) (PreH13 : (0 <= minimumIndex_2)) (PreH14 : (minimumIndex_2 <= maximumIndex_2)) (PreH15 : (maximumIndex_2 < heightSize_pre)) (PreH16 : (0 <= currentHeight_2)) (PreH17 : (currentHeight_2 <= 10000)) (PreH18 : (0 <= distanceToMinimum_2)) (PreH19 : (distanceToMinimum_2 <= 99999)) (PreH20 : (0 <= distanceToMaximum_2)) (PreH21 : (distanceToMaximum_2 <= 99999)) (PreH22 : (distanceToMinimum_2 = (minimumIndex_2 - index_2 ))) (PreH23 : (distanceToMaximum_2 = (maximumIndex_2 - index_2 ))) (PreH24 : (distanceToMinimum_2 <= width_2)) (PreH25 : (distanceToMaximum_2 <= width_2)) (PreH26 : (width_2 = distanceToMaximum_2)) (PreH27 : (0 <= width_2)) (PreH28 : (width_2 <= 99999)) (PreH29 : (0 <= maximumArea_2)) (PreH30 : (maximumArea_2 <= 999990000)) (PreH31 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH32 : (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2 )) (PreH33 : (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2 )) (PreH34 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k_2)
  **  ((( &( "index" ) )) # Int  |-> index_2)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight_2)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex_2)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex_2)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "width" ) )) # Int  |-> width_2)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea_2)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  (EX (k: Z)  (index: Z)  (currentHeight: Z)  (minimumIndex: Z)  (maximumIndex: Z)  (distanceToMinimum: Z)  (distanceToMaximum: Z)  (width: Z)  (maximumArea: Z) ,
  “ (distanceToMaximum = distanceToMaximum) ” 
  &&  “ (distanceToMinimum <= INT_MAX) ” 
  &&  “ (maximumIndex <= INT_MAX) ” 
  &&  “ (minimumIndex <= INT_MAX) ” 
  &&  “ (currentHeight <= INT_MAX) ” 
  &&  “ (index <= INT_MAX) ” 
  &&  “ (k <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width * currentHeight ) <= INT_MAX) ” 
  &&  “ (distanceToMinimum >= INT_MIN) ” 
  &&  “ (maximumIndex >= INT_MIN) ” 
  &&  “ (minimumIndex >= INT_MIN) ” 
  &&  “ (currentHeight >= INT_MIN) ” 
  &&  “ (index >= INT_MIN) ” 
  &&  “ (k >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width * currentHeight ) >= INT_MIN) ” 
  &&  “ (index < minimumIndex) ” 
  &&  “ ((width * currentHeight ) > maximumArea) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ (index = (Znth k sorted_i 0)) ” 
  &&  “ (currentHeight = (Znth k sorted_h 0)) ” 
  &&  “ (currentHeight = (Znth index l 0)) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= currentHeight) ” 
  &&  “ (currentHeight <= 10000) ” 
  &&  “ (0 <= distanceToMinimum) ” 
  &&  “ (distanceToMinimum <= 99999) ” 
  &&  “ (0 <= distanceToMaximum) ” 
  &&  “ (distanceToMaximum <= 99999) ” 
  &&  “ (distanceToMinimum = (minimumIndex - index )) ” 
  &&  “ (distanceToMaximum = (maximumIndex - index )) ” 
  &&  “ (distanceToMinimum <= width) ” 
  &&  “ (distanceToMaximum <= width) ” 
  &&  “ (width = distanceToMinimum) ” 
  &&  “ (0 <= width) ” 
  &&  “ (width <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (EX (k: Z)  (index: Z)  (currentHeight: Z)  (minimumIndex: Z)  (maximumIndex: Z)  (distanceToMinimum: Z)  (distanceToMaximum: Z)  (width: Z)  (maximumArea: Z) ,
  “ (distanceToMaximum = distanceToMaximum) ” 
  &&  “ (maximumArea <= INT_MAX) ” 
  &&  “ (distanceToMinimum <= INT_MAX) ” 
  &&  “ (maximumIndex <= INT_MAX) ” 
  &&  “ (minimumIndex <= INT_MAX) ” 
  &&  “ (currentHeight <= INT_MAX) ” 
  &&  “ (index <= INT_MAX) ” 
  &&  “ (k <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width * currentHeight ) <= INT_MAX) ” 
  &&  “ (maximumArea >= INT_MIN) ” 
  &&  “ (distanceToMinimum >= INT_MIN) ” 
  &&  “ (maximumIndex >= INT_MIN) ” 
  &&  “ (minimumIndex >= INT_MIN) ” 
  &&  “ (currentHeight >= INT_MIN) ” 
  &&  “ (index >= INT_MIN) ” 
  &&  “ (k >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width * currentHeight ) >= INT_MIN) ” 
  &&  “ (index < minimumIndex) ” 
  &&  “ ((width * currentHeight ) <= maximumArea) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ (index = (Znth k sorted_i 0)) ” 
  &&  “ (currentHeight = (Znth k sorted_h 0)) ” 
  &&  “ (currentHeight = (Znth index l 0)) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= currentHeight) ” 
  &&  “ (currentHeight <= 10000) ” 
  &&  “ (0 <= distanceToMinimum) ” 
  &&  “ (distanceToMinimum <= 99999) ” 
  &&  “ (0 <= distanceToMaximum) ” 
  &&  “ (distanceToMaximum <= 99999) ” 
  &&  “ (distanceToMinimum = (minimumIndex - index )) ” 
  &&  “ (distanceToMaximum = (maximumIndex - index )) ” 
  &&  “ (distanceToMinimum <= width) ” 
  &&  “ (distanceToMaximum <= width) ” 
  &&  “ (width = distanceToMinimum) ” 
  &&  “ (0 <= width) ” 
  &&  “ (width <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (“ (distanceToMaximum_2 = distanceToMaximum_2) ” 
  &&  “ (maximumArea_2 <= INT_MAX) ” 
  &&  “ (distanceToMinimum_2 <= INT_MAX) ” 
  &&  “ (maximumIndex_2 <= INT_MAX) ” 
  &&  “ (minimumIndex_2 <= INT_MAX) ” 
  &&  “ (currentHeight_2 <= INT_MAX) ” 
  &&  “ (index_2 <= INT_MAX) ” 
  &&  “ (k_2 <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width_2 * currentHeight_2 ) <= INT_MAX) ” 
  &&  “ (maximumArea_2 >= INT_MIN) ” 
  &&  “ (distanceToMinimum_2 >= INT_MIN) ” 
  &&  “ (maximumIndex_2 >= INT_MIN) ” 
  &&  “ (minimumIndex_2 >= INT_MIN) ” 
  &&  “ (currentHeight_2 >= INT_MIN) ” 
  &&  “ (index_2 >= INT_MIN) ” 
  &&  “ (k_2 >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width_2 * currentHeight_2 ) >= INT_MIN) ” 
  &&  “ (index_2 < minimumIndex_2) ” 
  &&  “ ((width_2 * currentHeight_2 ) <= maximumArea_2) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k_2) ” 
  &&  “ (k_2 < heightSize_pre) ” 
  &&  “ (index_2 = (Znth k_2 sorted_i 0)) ” 
  &&  “ (currentHeight_2 = (Znth k_2 sorted_h 0)) ” 
  &&  “ (currentHeight_2 = (Znth index_2 l 0)) ” 
  &&  “ (0 <= index_2) ” 
  &&  “ (index_2 < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex_2) ” 
  &&  “ (minimumIndex_2 <= maximumIndex_2) ” 
  &&  “ (maximumIndex_2 < heightSize_pre) ” 
  &&  “ (0 <= currentHeight_2) ” 
  &&  “ (currentHeight_2 <= 10000) ” 
  &&  “ (0 <= distanceToMinimum_2) ” 
  &&  “ (distanceToMinimum_2 <= 99999) ” 
  &&  “ (0 <= distanceToMaximum_2) ” 
  &&  “ (distanceToMaximum_2 <= 99999) ” 
  &&  “ (distanceToMinimum_2 = (minimumIndex_2 - index_2 )) ” 
  &&  “ (distanceToMaximum_2 = (maximumIndex_2 - index_2 )) ” 
  &&  “ (distanceToMinimum_2 <= width_2) ” 
  &&  “ (distanceToMaximum_2 <= width_2) ” 
  &&  “ (width_2 = distanceToMaximum_2) ” 
  &&  “ (0 <= width_2) ” 
  &&  “ (width_2 <= 99999) ” 
  &&  “ (0 <= maximumArea_2) ” 
  &&  “ (maximumArea_2 <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2 ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2 ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "width" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "area" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k_2)
  **  ((( &( "index" ) )) # Int  |-> index_2)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight_2)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex_2)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex_2)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea_2)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
.

Definition maxAreaNLogN_entail_wit_8_1 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  (“ (distanceToMinimum = distanceToMinimum) ” 
  &&  “ (distanceToMaximum <= INT_MAX) ” 
  &&  “ (maximumIndex <= INT_MAX) ” 
  &&  “ (minimumIndex <= INT_MAX) ” 
  &&  “ (currentHeight <= INT_MAX) ” 
  &&  “ (index <= INT_MAX) ” 
  &&  “ (k <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width * currentHeight ) <= INT_MAX) ” 
  &&  “ (distanceToMaximum >= INT_MIN) ” 
  &&  “ (maximumIndex >= INT_MIN) ” 
  &&  “ (minimumIndex >= INT_MIN) ” 
  &&  “ (currentHeight >= INT_MIN) ” 
  &&  “ (index >= INT_MIN) ” 
  &&  “ (k >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width * currentHeight ) >= INT_MIN) ” 
  &&  “ (index > maximumIndex) ” 
  &&  “ (index >= minimumIndex) ” 
  &&  “ ((width * currentHeight ) > maximumArea) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ (index = (Znth k sorted_i 0)) ” 
  &&  “ (currentHeight = (Znth k sorted_h 0)) ” 
  &&  “ (currentHeight = (Znth index l 0)) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= currentHeight) ” 
  &&  “ (currentHeight <= 10000) ” 
  &&  “ (0 <= distanceToMinimum) ” 
  &&  “ (distanceToMinimum <= 99999) ” 
  &&  “ (0 <= distanceToMaximum) ” 
  &&  “ (distanceToMaximum <= 99999) ” 
  &&  “ (distanceToMinimum = (index - minimumIndex )) ” 
  &&  “ (distanceToMaximum = (index - maximumIndex )) ” 
  &&  “ (distanceToMinimum <= width) ” 
  &&  “ (distanceToMaximum <= width) ” 
  &&  “ (width = distanceToMinimum) ” 
  &&  “ (0 <= width) ” 
  &&  “ (width <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "width" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (EX (k_2: Z)  (index_2: Z)  (currentHeight_2: Z)  (minimumIndex_2: Z)  (maximumIndex_2: Z)  (distanceToMinimum_2: Z)  (distanceToMaximum_2: Z)  (width_2: Z)  (maximumArea_2: Z) ,
  “ (distanceToMinimum_2 = distanceToMinimum_2) ” 
  &&  “ (distanceToMaximum_2 <= INT_MAX) ” 
  &&  “ (maximumIndex_2 <= INT_MAX) ” 
  &&  “ (minimumIndex_2 <= INT_MAX) ” 
  &&  “ (currentHeight_2 <= INT_MAX) ” 
  &&  “ (index_2 <= INT_MAX) ” 
  &&  “ (k_2 <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width_2 * currentHeight_2 ) <= INT_MAX) ” 
  &&  “ (distanceToMaximum_2 >= INT_MIN) ” 
  &&  “ (maximumIndex_2 >= INT_MIN) ” 
  &&  “ (minimumIndex_2 >= INT_MIN) ” 
  &&  “ (currentHeight_2 >= INT_MIN) ” 
  &&  “ (index_2 >= INT_MIN) ” 
  &&  “ (k_2 >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width_2 * currentHeight_2 ) >= INT_MIN) ” 
  &&  “ (index_2 > maximumIndex_2) ” 
  &&  “ (index_2 >= minimumIndex_2) ” 
  &&  “ ((width_2 * currentHeight_2 ) > maximumArea_2) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k_2) ” 
  &&  “ (k_2 < heightSize_pre) ” 
  &&  “ (index_2 = (Znth k_2 sorted_i 0)) ” 
  &&  “ (currentHeight_2 = (Znth k_2 sorted_h 0)) ” 
  &&  “ (currentHeight_2 = (Znth index_2 l 0)) ” 
  &&  “ (0 <= index_2) ” 
  &&  “ (index_2 < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex_2) ” 
  &&  “ (minimumIndex_2 <= maximumIndex_2) ” 
  &&  “ (maximumIndex_2 < heightSize_pre) ” 
  &&  “ (0 <= currentHeight_2) ” 
  &&  “ (currentHeight_2 <= 10000) ” 
  &&  “ (0 <= distanceToMinimum_2) ” 
  &&  “ (distanceToMinimum_2 <= 99999) ” 
  &&  “ (0 <= distanceToMaximum_2) ” 
  &&  “ (distanceToMaximum_2 <= 99999) ” 
  &&  “ (distanceToMinimum_2 = (index_2 - minimumIndex_2 )) ” 
  &&  “ (distanceToMaximum_2 = (index_2 - maximumIndex_2 )) ” 
  &&  “ (distanceToMinimum_2 <= width_2) ” 
  &&  “ (distanceToMaximum_2 <= width_2) ” 
  &&  “ (width_2 = distanceToMaximum_2) ” 
  &&  “ (0 <= width_2) ” 
  &&  “ (width_2 <= 99999) ” 
  &&  “ (0 <= maximumArea_2) ” 
  &&  “ (maximumArea_2 <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2 ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2 ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "width" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "area" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k_2)
  **  ((( &( "index" ) )) # Int  |-> index_2)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight_2)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex_2)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex_2)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (EX (k_2: Z)  (index_2: Z)  (currentHeight_2: Z)  (minimumIndex_2: Z)  (maximumIndex_2: Z)  (distanceToMinimum_2: Z)  (distanceToMaximum_2: Z)  (width_2: Z)  (maximumArea_2: Z) ,
  “ (distanceToMinimum_2 = distanceToMinimum_2) ” 
  &&  “ (maximumArea_2 <= INT_MAX) ” 
  &&  “ (distanceToMaximum_2 <= INT_MAX) ” 
  &&  “ (maximumIndex_2 <= INT_MAX) ” 
  &&  “ (minimumIndex_2 <= INT_MAX) ” 
  &&  “ (currentHeight_2 <= INT_MAX) ” 
  &&  “ (index_2 <= INT_MAX) ” 
  &&  “ (k_2 <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width_2 * currentHeight_2 ) <= INT_MAX) ” 
  &&  “ (maximumArea_2 >= INT_MIN) ” 
  &&  “ (distanceToMaximum_2 >= INT_MIN) ” 
  &&  “ (maximumIndex_2 >= INT_MIN) ” 
  &&  “ (minimumIndex_2 >= INT_MIN) ” 
  &&  “ (currentHeight_2 >= INT_MIN) ” 
  &&  “ (index_2 >= INT_MIN) ” 
  &&  “ (k_2 >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width_2 * currentHeight_2 ) >= INT_MIN) ” 
  &&  “ (index_2 > maximumIndex_2) ” 
  &&  “ (index_2 >= minimumIndex_2) ” 
  &&  “ ((width_2 * currentHeight_2 ) <= maximumArea_2) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k_2) ” 
  &&  “ (k_2 < heightSize_pre) ” 
  &&  “ (index_2 = (Znth k_2 sorted_i 0)) ” 
  &&  “ (currentHeight_2 = (Znth k_2 sorted_h 0)) ” 
  &&  “ (currentHeight_2 = (Znth index_2 l 0)) ” 
  &&  “ (0 <= index_2) ” 
  &&  “ (index_2 < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex_2) ” 
  &&  “ (minimumIndex_2 <= maximumIndex_2) ” 
  &&  “ (maximumIndex_2 < heightSize_pre) ” 
  &&  “ (0 <= currentHeight_2) ” 
  &&  “ (currentHeight_2 <= 10000) ” 
  &&  “ (0 <= distanceToMinimum_2) ” 
  &&  “ (distanceToMinimum_2 <= 99999) ” 
  &&  “ (0 <= distanceToMaximum_2) ” 
  &&  “ (distanceToMaximum_2 <= 99999) ” 
  &&  “ (distanceToMinimum_2 = (index_2 - minimumIndex_2 )) ” 
  &&  “ (distanceToMaximum_2 = (index_2 - maximumIndex_2 )) ” 
  &&  “ (distanceToMinimum_2 <= width_2) ” 
  &&  “ (distanceToMaximum_2 <= width_2) ” 
  &&  “ (width_2 = distanceToMaximum_2) ” 
  &&  “ (0 <= width_2) ” 
  &&  “ (width_2 <= 99999) ” 
  &&  “ (0 <= maximumArea_2) ” 
  &&  “ (maximumArea_2 <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2 ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2 ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "width" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "area" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k_2)
  **  ((( &( "index" ) )) # Int  |-> index_2)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight_2)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex_2)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex_2)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea_2)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
.

Definition maxAreaNLogN_entail_wit_8_2 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k_2: Z) (index_2: Z) (currentHeight_2: Z) (minimumIndex_2: Z) (maximumIndex_2: Z) (distanceToMinimum_2: Z) (distanceToMaximum_2: Z) (width_2: Z) (maximumArea_2: Z) (PreH1 : (index_2 > maximumIndex_2)) (PreH2 : (index_2 >= minimumIndex_2)) (PreH3 : ((width_2 * currentHeight_2 ) > maximumArea_2)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k_2)) (PreH8 : (k_2 < heightSize_pre)) (PreH9 : (index_2 = (Znth k_2 sorted_i 0))) (PreH10 : (currentHeight_2 = (Znth k_2 sorted_h 0))) (PreH11 : (currentHeight_2 = (Znth index_2 l 0))) (PreH12 : (0 <= index_2)) (PreH13 : (index_2 < heightSize_pre)) (PreH14 : (0 <= minimumIndex_2)) (PreH15 : (minimumIndex_2 <= maximumIndex_2)) (PreH16 : (maximumIndex_2 < heightSize_pre)) (PreH17 : (0 <= currentHeight_2)) (PreH18 : (currentHeight_2 <= 10000)) (PreH19 : (0 <= distanceToMinimum_2)) (PreH20 : (distanceToMinimum_2 <= 99999)) (PreH21 : (0 <= distanceToMaximum_2)) (PreH22 : (distanceToMaximum_2 <= 99999)) (PreH23 : (distanceToMinimum_2 = (index_2 - minimumIndex_2 ))) (PreH24 : (distanceToMaximum_2 = (index_2 - maximumIndex_2 ))) (PreH25 : (distanceToMinimum_2 <= width_2)) (PreH26 : (distanceToMaximum_2 <= width_2)) (PreH27 : (width_2 = distanceToMaximum_2)) (PreH28 : (0 <= width_2)) (PreH29 : (width_2 <= 99999)) (PreH30 : (0 <= maximumArea_2)) (PreH31 : (maximumArea_2 <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2 )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2 )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k_2)
  **  ((( &( "index" ) )) # Int  |-> index_2)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight_2)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex_2)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex_2)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "width" ) )) # Int  |-> width_2)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  (EX (k: Z)  (index: Z)  (currentHeight: Z)  (minimumIndex: Z)  (maximumIndex: Z)  (distanceToMinimum: Z)  (distanceToMaximum: Z)  (width: Z)  (maximumArea: Z) ,
  “ (distanceToMinimum = distanceToMinimum) ” 
  &&  “ (distanceToMaximum <= INT_MAX) ” 
  &&  “ (maximumIndex <= INT_MAX) ” 
  &&  “ (minimumIndex <= INT_MAX) ” 
  &&  “ (currentHeight <= INT_MAX) ” 
  &&  “ (index <= INT_MAX) ” 
  &&  “ (k <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width * currentHeight ) <= INT_MAX) ” 
  &&  “ (distanceToMaximum >= INT_MIN) ” 
  &&  “ (maximumIndex >= INT_MIN) ” 
  &&  “ (minimumIndex >= INT_MIN) ” 
  &&  “ (currentHeight >= INT_MIN) ” 
  &&  “ (index >= INT_MIN) ” 
  &&  “ (k >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width * currentHeight ) >= INT_MIN) ” 
  &&  “ (index > maximumIndex) ” 
  &&  “ (index >= minimumIndex) ” 
  &&  “ ((width * currentHeight ) > maximumArea) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ (index = (Znth k sorted_i 0)) ” 
  &&  “ (currentHeight = (Znth k sorted_h 0)) ” 
  &&  “ (currentHeight = (Znth index l 0)) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= currentHeight) ” 
  &&  “ (currentHeight <= 10000) ” 
  &&  “ (0 <= distanceToMinimum) ” 
  &&  “ (distanceToMinimum <= 99999) ” 
  &&  “ (0 <= distanceToMaximum) ” 
  &&  “ (distanceToMaximum <= 99999) ” 
  &&  “ (distanceToMinimum = (index - minimumIndex )) ” 
  &&  “ (distanceToMaximum = (index - maximumIndex )) ” 
  &&  “ (distanceToMinimum <= width) ” 
  &&  “ (distanceToMaximum <= width) ” 
  &&  “ (width = distanceToMinimum) ” 
  &&  “ (0 <= width) ” 
  &&  “ (width <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "width" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (“ (distanceToMinimum_2 = distanceToMinimum_2) ” 
  &&  “ (distanceToMaximum_2 <= INT_MAX) ” 
  &&  “ (maximumIndex_2 <= INT_MAX) ” 
  &&  “ (minimumIndex_2 <= INT_MAX) ” 
  &&  “ (currentHeight_2 <= INT_MAX) ” 
  &&  “ (index_2 <= INT_MAX) ” 
  &&  “ (k_2 <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width_2 * currentHeight_2 ) <= INT_MAX) ” 
  &&  “ (distanceToMaximum_2 >= INT_MIN) ” 
  &&  “ (maximumIndex_2 >= INT_MIN) ” 
  &&  “ (minimumIndex_2 >= INT_MIN) ” 
  &&  “ (currentHeight_2 >= INT_MIN) ” 
  &&  “ (index_2 >= INT_MIN) ” 
  &&  “ (k_2 >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width_2 * currentHeight_2 ) >= INT_MIN) ” 
  &&  “ (index_2 > maximumIndex_2) ” 
  &&  “ (index_2 >= minimumIndex_2) ” 
  &&  “ ((width_2 * currentHeight_2 ) > maximumArea_2) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k_2) ” 
  &&  “ (k_2 < heightSize_pre) ” 
  &&  “ (index_2 = (Znth k_2 sorted_i 0)) ” 
  &&  “ (currentHeight_2 = (Znth k_2 sorted_h 0)) ” 
  &&  “ (currentHeight_2 = (Znth index_2 l 0)) ” 
  &&  “ (0 <= index_2) ” 
  &&  “ (index_2 < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex_2) ” 
  &&  “ (minimumIndex_2 <= maximumIndex_2) ” 
  &&  “ (maximumIndex_2 < heightSize_pre) ” 
  &&  “ (0 <= currentHeight_2) ” 
  &&  “ (currentHeight_2 <= 10000) ” 
  &&  “ (0 <= distanceToMinimum_2) ” 
  &&  “ (distanceToMinimum_2 <= 99999) ” 
  &&  “ (0 <= distanceToMaximum_2) ” 
  &&  “ (distanceToMaximum_2 <= 99999) ” 
  &&  “ (distanceToMinimum_2 = (index_2 - minimumIndex_2 )) ” 
  &&  “ (distanceToMaximum_2 = (index_2 - maximumIndex_2 )) ” 
  &&  “ (distanceToMinimum_2 <= width_2) ” 
  &&  “ (distanceToMaximum_2 <= width_2) ” 
  &&  “ (width_2 = distanceToMaximum_2) ” 
  &&  “ (0 <= width_2) ” 
  &&  “ (width_2 <= 99999) ” 
  &&  “ (0 <= maximumArea_2) ” 
  &&  “ (maximumArea_2 <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2 ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2 ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "width" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "area" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k_2)
  **  ((( &( "index" ) )) # Int  |-> index_2)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight_2)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex_2)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex_2)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (EX (k: Z)  (index: Z)  (currentHeight: Z)  (minimumIndex: Z)  (maximumIndex: Z)  (distanceToMinimum: Z)  (distanceToMaximum: Z)  (width: Z)  (maximumArea: Z) ,
  “ (distanceToMinimum = distanceToMinimum) ” 
  &&  “ (maximumArea <= INT_MAX) ” 
  &&  “ (distanceToMaximum <= INT_MAX) ” 
  &&  “ (maximumIndex <= INT_MAX) ” 
  &&  “ (minimumIndex <= INT_MAX) ” 
  &&  “ (currentHeight <= INT_MAX) ” 
  &&  “ (index <= INT_MAX) ” 
  &&  “ (k <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width * currentHeight ) <= INT_MAX) ” 
  &&  “ (maximumArea >= INT_MIN) ” 
  &&  “ (distanceToMaximum >= INT_MIN) ” 
  &&  “ (maximumIndex >= INT_MIN) ” 
  &&  “ (minimumIndex >= INT_MIN) ” 
  &&  “ (currentHeight >= INT_MIN) ” 
  &&  “ (index >= INT_MIN) ” 
  &&  “ (k >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width * currentHeight ) >= INT_MIN) ” 
  &&  “ (index > maximumIndex) ” 
  &&  “ (index >= minimumIndex) ” 
  &&  “ ((width * currentHeight ) <= maximumArea) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ (index = (Znth k sorted_i 0)) ” 
  &&  “ (currentHeight = (Znth k sorted_h 0)) ” 
  &&  “ (currentHeight = (Znth index l 0)) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= currentHeight) ” 
  &&  “ (currentHeight <= 10000) ” 
  &&  “ (0 <= distanceToMinimum) ” 
  &&  “ (distanceToMinimum <= 99999) ” 
  &&  “ (0 <= distanceToMaximum) ” 
  &&  “ (distanceToMaximum <= 99999) ” 
  &&  “ (distanceToMinimum = (index - minimumIndex )) ” 
  &&  “ (distanceToMaximum = (index - maximumIndex )) ” 
  &&  “ (distanceToMinimum <= width) ” 
  &&  “ (distanceToMaximum <= width) ” 
  &&  “ (width = distanceToMinimum) ” 
  &&  “ (0 <= width) ” 
  &&  “ (width <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "width" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
.

Definition maxAreaNLogN_entail_wit_8_3 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index > maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i 0))) (PreH10 : (currentHeight = (Znth k sorted_h 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  (EX (k_2: Z)  (index_2: Z)  (currentHeight_2: Z)  (minimumIndex_2: Z)  (maximumIndex_2: Z)  (distanceToMinimum_2: Z)  (distanceToMaximum_2: Z)  (width_2: Z)  (maximumArea_2: Z) ,
  “ (distanceToMinimum_2 = distanceToMinimum_2) ” 
  &&  “ (distanceToMaximum_2 <= INT_MAX) ” 
  &&  “ (maximumIndex_2 <= INT_MAX) ” 
  &&  “ (minimumIndex_2 <= INT_MAX) ” 
  &&  “ (currentHeight_2 <= INT_MAX) ” 
  &&  “ (index_2 <= INT_MAX) ” 
  &&  “ (k_2 <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width_2 * currentHeight_2 ) <= INT_MAX) ” 
  &&  “ (distanceToMaximum_2 >= INT_MIN) ” 
  &&  “ (maximumIndex_2 >= INT_MIN) ” 
  &&  “ (minimumIndex_2 >= INT_MIN) ” 
  &&  “ (currentHeight_2 >= INT_MIN) ” 
  &&  “ (index_2 >= INT_MIN) ” 
  &&  “ (k_2 >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width_2 * currentHeight_2 ) >= INT_MIN) ” 
  &&  “ (index_2 > maximumIndex_2) ” 
  &&  “ (index_2 >= minimumIndex_2) ” 
  &&  “ ((width_2 * currentHeight_2 ) > maximumArea_2) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k_2) ” 
  &&  “ (k_2 < heightSize_pre) ” 
  &&  “ (index_2 = (Znth k_2 sorted_i 0)) ” 
  &&  “ (currentHeight_2 = (Znth k_2 sorted_h 0)) ” 
  &&  “ (currentHeight_2 = (Znth index_2 l 0)) ” 
  &&  “ (0 <= index_2) ” 
  &&  “ (index_2 < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex_2) ” 
  &&  “ (minimumIndex_2 <= maximumIndex_2) ” 
  &&  “ (maximumIndex_2 < heightSize_pre) ” 
  &&  “ (0 <= currentHeight_2) ” 
  &&  “ (currentHeight_2 <= 10000) ” 
  &&  “ (0 <= distanceToMinimum_2) ” 
  &&  “ (distanceToMinimum_2 <= 99999) ” 
  &&  “ (0 <= distanceToMaximum_2) ” 
  &&  “ (distanceToMaximum_2 <= 99999) ” 
  &&  “ (distanceToMinimum_2 = (index_2 - minimumIndex_2 )) ” 
  &&  “ (distanceToMaximum_2 = (index_2 - maximumIndex_2 )) ” 
  &&  “ (distanceToMinimum_2 <= width_2) ” 
  &&  “ (distanceToMaximum_2 <= width_2) ” 
  &&  “ (width_2 = distanceToMaximum_2) ” 
  &&  “ (0 <= width_2) ” 
  &&  “ (width_2 <= 99999) ” 
  &&  “ (0 <= maximumArea_2) ” 
  &&  “ (maximumArea_2 <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2 ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2 ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "width" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "area" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k_2)
  **  ((( &( "index" ) )) # Int  |-> index_2)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight_2)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex_2)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex_2)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (“ (distanceToMinimum = distanceToMinimum) ” 
  &&  “ (maximumArea <= INT_MAX) ” 
  &&  “ (distanceToMaximum <= INT_MAX) ” 
  &&  “ (maximumIndex <= INT_MAX) ” 
  &&  “ (minimumIndex <= INT_MAX) ” 
  &&  “ (currentHeight <= INT_MAX) ” 
  &&  “ (index <= INT_MAX) ” 
  &&  “ (k <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width * currentHeight ) <= INT_MAX) ” 
  &&  “ (maximumArea >= INT_MIN) ” 
  &&  “ (distanceToMaximum >= INT_MIN) ” 
  &&  “ (maximumIndex >= INT_MIN) ” 
  &&  “ (minimumIndex >= INT_MIN) ” 
  &&  “ (currentHeight >= INT_MIN) ” 
  &&  “ (index >= INT_MIN) ” 
  &&  “ (k >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width * currentHeight ) >= INT_MIN) ” 
  &&  “ (index > maximumIndex) ” 
  &&  “ (index >= minimumIndex) ” 
  &&  “ ((width * currentHeight ) <= maximumArea) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ (index = (Znth k sorted_i 0)) ” 
  &&  “ (currentHeight = (Znth k sorted_h 0)) ” 
  &&  “ (currentHeight = (Znth index l 0)) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= currentHeight) ” 
  &&  “ (currentHeight <= 10000) ” 
  &&  “ (0 <= distanceToMinimum) ” 
  &&  “ (distanceToMinimum <= 99999) ” 
  &&  “ (0 <= distanceToMaximum) ” 
  &&  “ (distanceToMaximum <= 99999) ” 
  &&  “ (distanceToMinimum = (index - minimumIndex )) ” 
  &&  “ (distanceToMaximum = (index - maximumIndex )) ” 
  &&  “ (distanceToMinimum <= width) ” 
  &&  “ (distanceToMaximum <= width) ” 
  &&  “ (width = distanceToMinimum) ” 
  &&  “ (0 <= width) ” 
  &&  “ (width <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "width" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (EX (k_2: Z)  (index_2: Z)  (currentHeight_2: Z)  (minimumIndex_2: Z)  (maximumIndex_2: Z)  (distanceToMinimum_2: Z)  (distanceToMaximum_2: Z)  (width_2: Z)  (maximumArea_2: Z) ,
  “ (distanceToMinimum_2 = distanceToMinimum_2) ” 
  &&  “ (maximumArea_2 <= INT_MAX) ” 
  &&  “ (distanceToMaximum_2 <= INT_MAX) ” 
  &&  “ (maximumIndex_2 <= INT_MAX) ” 
  &&  “ (minimumIndex_2 <= INT_MAX) ” 
  &&  “ (currentHeight_2 <= INT_MAX) ” 
  &&  “ (index_2 <= INT_MAX) ” 
  &&  “ (k_2 <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width_2 * currentHeight_2 ) <= INT_MAX) ” 
  &&  “ (maximumArea_2 >= INT_MIN) ” 
  &&  “ (distanceToMaximum_2 >= INT_MIN) ” 
  &&  “ (maximumIndex_2 >= INT_MIN) ” 
  &&  “ (minimumIndex_2 >= INT_MIN) ” 
  &&  “ (currentHeight_2 >= INT_MIN) ” 
  &&  “ (index_2 >= INT_MIN) ” 
  &&  “ (k_2 >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width_2 * currentHeight_2 ) >= INT_MIN) ” 
  &&  “ (index_2 > maximumIndex_2) ” 
  &&  “ (index_2 >= minimumIndex_2) ” 
  &&  “ ((width_2 * currentHeight_2 ) <= maximumArea_2) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k_2) ” 
  &&  “ (k_2 < heightSize_pre) ” 
  &&  “ (index_2 = (Znth k_2 sorted_i 0)) ” 
  &&  “ (currentHeight_2 = (Znth k_2 sorted_h 0)) ” 
  &&  “ (currentHeight_2 = (Znth index_2 l 0)) ” 
  &&  “ (0 <= index_2) ” 
  &&  “ (index_2 < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex_2) ” 
  &&  “ (minimumIndex_2 <= maximumIndex_2) ” 
  &&  “ (maximumIndex_2 < heightSize_pre) ” 
  &&  “ (0 <= currentHeight_2) ” 
  &&  “ (currentHeight_2 <= 10000) ” 
  &&  “ (0 <= distanceToMinimum_2) ” 
  &&  “ (distanceToMinimum_2 <= 99999) ” 
  &&  “ (0 <= distanceToMaximum_2) ” 
  &&  “ (distanceToMaximum_2 <= 99999) ” 
  &&  “ (distanceToMinimum_2 = (index_2 - minimumIndex_2 )) ” 
  &&  “ (distanceToMaximum_2 = (index_2 - maximumIndex_2 )) ” 
  &&  “ (distanceToMinimum_2 <= width_2) ” 
  &&  “ (distanceToMaximum_2 <= width_2) ” 
  &&  “ (width_2 = distanceToMaximum_2) ” 
  &&  “ (0 <= width_2) ” 
  &&  “ (width_2 <= 99999) ” 
  &&  “ (0 <= maximumArea_2) ” 
  &&  “ (maximumArea_2 <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2 ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2 ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "width" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "area" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k_2)
  **  ((( &( "index" ) )) # Int  |-> index_2)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight_2)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex_2)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex_2)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea_2)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
.

Definition maxAreaNLogN_entail_wit_8_4 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (k_2: Z) (index_2: Z) (currentHeight_2: Z) (minimumIndex_2: Z) (maximumIndex_2: Z) (distanceToMinimum_2: Z) (distanceToMaximum_2: Z) (width_2: Z) (maximumArea_2: Z) (PreH1 : (index_2 > maximumIndex_2)) (PreH2 : (index_2 >= minimumIndex_2)) (PreH3 : ((width_2 * currentHeight_2 ) <= maximumArea_2)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k_2)) (PreH8 : (k_2 < heightSize_pre)) (PreH9 : (index_2 = (Znth k_2 sorted_i 0))) (PreH10 : (currentHeight_2 = (Znth k_2 sorted_h 0))) (PreH11 : (currentHeight_2 = (Znth index_2 l 0))) (PreH12 : (0 <= index_2)) (PreH13 : (index_2 < heightSize_pre)) (PreH14 : (0 <= minimumIndex_2)) (PreH15 : (minimumIndex_2 <= maximumIndex_2)) (PreH16 : (maximumIndex_2 < heightSize_pre)) (PreH17 : (0 <= currentHeight_2)) (PreH18 : (currentHeight_2 <= 10000)) (PreH19 : (0 <= distanceToMinimum_2)) (PreH20 : (distanceToMinimum_2 <= 99999)) (PreH21 : (0 <= distanceToMaximum_2)) (PreH22 : (distanceToMaximum_2 <= 99999)) (PreH23 : (distanceToMinimum_2 = (index_2 - minimumIndex_2 ))) (PreH24 : (distanceToMaximum_2 = (index_2 - maximumIndex_2 ))) (PreH25 : (distanceToMinimum_2 <= width_2)) (PreH26 : (distanceToMaximum_2 <= width_2)) (PreH27 : (width_2 = distanceToMaximum_2)) (PreH28 : (0 <= width_2)) (PreH29 : (width_2 <= 99999)) (PreH30 : (0 <= maximumArea_2)) (PreH31 : (maximumArea_2 <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2 )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2 )) (PreH35 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "area" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k_2)
  **  ((( &( "index" ) )) # Int  |-> index_2)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight_2)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex_2)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex_2)
  **  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "width" ) )) # Int  |-> width_2)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea_2)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  (EX (k: Z)  (index: Z)  (currentHeight: Z)  (minimumIndex: Z)  (maximumIndex: Z)  (distanceToMinimum: Z)  (distanceToMaximum: Z)  (width: Z)  (maximumArea: Z) ,
  “ (distanceToMinimum = distanceToMinimum) ” 
  &&  “ (distanceToMaximum <= INT_MAX) ” 
  &&  “ (maximumIndex <= INT_MAX) ” 
  &&  “ (minimumIndex <= INT_MAX) ” 
  &&  “ (currentHeight <= INT_MAX) ” 
  &&  “ (index <= INT_MAX) ” 
  &&  “ (k <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width * currentHeight ) <= INT_MAX) ” 
  &&  “ (distanceToMaximum >= INT_MIN) ” 
  &&  “ (maximumIndex >= INT_MIN) ” 
  &&  “ (minimumIndex >= INT_MIN) ” 
  &&  “ (currentHeight >= INT_MIN) ” 
  &&  “ (index >= INT_MIN) ” 
  &&  “ (k >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width * currentHeight ) >= INT_MIN) ” 
  &&  “ (index > maximumIndex) ” 
  &&  “ (index >= minimumIndex) ” 
  &&  “ ((width * currentHeight ) > maximumArea) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ (index = (Znth k sorted_i 0)) ” 
  &&  “ (currentHeight = (Znth k sorted_h 0)) ” 
  &&  “ (currentHeight = (Znth index l 0)) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= currentHeight) ” 
  &&  “ (currentHeight <= 10000) ” 
  &&  “ (0 <= distanceToMinimum) ” 
  &&  “ (distanceToMinimum <= 99999) ” 
  &&  “ (0 <= distanceToMaximum) ” 
  &&  “ (distanceToMaximum <= 99999) ” 
  &&  “ (distanceToMinimum = (index - minimumIndex )) ” 
  &&  “ (distanceToMaximum = (index - maximumIndex )) ” 
  &&  “ (distanceToMinimum <= width) ” 
  &&  “ (distanceToMaximum <= width) ” 
  &&  “ (width = distanceToMinimum) ” 
  &&  “ (0 <= width) ” 
  &&  “ (width <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "width" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "maximumArea" ) )) # Int  |-> (width * currentHeight ))
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (EX (k: Z)  (index: Z)  (currentHeight: Z)  (minimumIndex: Z)  (maximumIndex: Z)  (distanceToMinimum: Z)  (distanceToMaximum: Z)  (width: Z)  (maximumArea: Z) ,
  “ (distanceToMinimum = distanceToMinimum) ” 
  &&  “ (maximumArea <= INT_MAX) ” 
  &&  “ (distanceToMaximum <= INT_MAX) ” 
  &&  “ (maximumIndex <= INT_MAX) ” 
  &&  “ (minimumIndex <= INT_MAX) ” 
  &&  “ (currentHeight <= INT_MAX) ” 
  &&  “ (index <= INT_MAX) ” 
  &&  “ (k <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width * currentHeight ) <= INT_MAX) ” 
  &&  “ (maximumArea >= INT_MIN) ” 
  &&  “ (distanceToMaximum >= INT_MIN) ” 
  &&  “ (maximumIndex >= INT_MIN) ” 
  &&  “ (minimumIndex >= INT_MIN) ” 
  &&  “ (currentHeight >= INT_MIN) ” 
  &&  “ (index >= INT_MIN) ” 
  &&  “ (k >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width * currentHeight ) >= INT_MIN) ” 
  &&  “ (index > maximumIndex) ” 
  &&  “ (index >= minimumIndex) ” 
  &&  “ ((width * currentHeight ) <= maximumArea) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < heightSize_pre) ” 
  &&  “ (index = (Znth k sorted_i 0)) ” 
  &&  “ (currentHeight = (Znth k sorted_h 0)) ” 
  &&  “ (currentHeight = (Znth index l 0)) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= currentHeight) ” 
  &&  “ (currentHeight <= 10000) ” 
  &&  “ (0 <= distanceToMinimum) ” 
  &&  “ (distanceToMinimum <= 99999) ” 
  &&  “ (0 <= distanceToMaximum) ” 
  &&  “ (distanceToMaximum <= 99999) ” 
  &&  “ (distanceToMinimum = (index - minimumIndex )) ” 
  &&  “ (distanceToMaximum = (index - maximumIndex )) ” 
  &&  “ (distanceToMinimum <= width) ” 
  &&  “ (distanceToMaximum <= width) ” 
  &&  “ (width = distanceToMinimum) ” 
  &&  “ (0 <= width) ” 
  &&  “ (width <= 99999) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "width" ) )) # Int  |-> distanceToMinimum)
  **  ((( &( "area" ) )) # Int  |-> (width * currentHeight ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
  ||
  (“ (distanceToMinimum_2 = distanceToMinimum_2) ” 
  &&  “ (maximumArea_2 <= INT_MAX) ” 
  &&  “ (distanceToMaximum_2 <= INT_MAX) ” 
  &&  “ (maximumIndex_2 <= INT_MAX) ” 
  &&  “ (minimumIndex_2 <= INT_MAX) ” 
  &&  “ (currentHeight_2 <= INT_MAX) ” 
  &&  “ (index_2 <= INT_MAX) ” 
  &&  “ (k_2 <= INT_MAX) ” 
  &&  “ (heightSize_pre <= INT_MAX) ” 
  &&  “ ((width_2 * currentHeight_2 ) <= INT_MAX) ” 
  &&  “ (maximumArea_2 >= INT_MIN) ” 
  &&  “ (distanceToMaximum_2 >= INT_MIN) ” 
  &&  “ (maximumIndex_2 >= INT_MIN) ” 
  &&  “ (minimumIndex_2 >= INT_MIN) ” 
  &&  “ (currentHeight_2 >= INT_MIN) ” 
  &&  “ (index_2 >= INT_MIN) ” 
  &&  “ (k_2 >= INT_MIN) ” 
  &&  “ (heightSize_pre >= INT_MIN) ” 
  &&  “ ((width_2 * currentHeight_2 ) >= INT_MIN) ” 
  &&  “ (index_2 > maximumIndex_2) ” 
  &&  “ (index_2 >= minimumIndex_2) ” 
  &&  “ ((width_2 * currentHeight_2 ) <= maximumArea_2) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k_2) ” 
  &&  “ (k_2 < heightSize_pre) ” 
  &&  “ (index_2 = (Znth k_2 sorted_i 0)) ” 
  &&  “ (currentHeight_2 = (Znth k_2 sorted_h 0)) ” 
  &&  “ (currentHeight_2 = (Znth index_2 l 0)) ” 
  &&  “ (0 <= index_2) ” 
  &&  “ (index_2 < heightSize_pre) ” 
  &&  “ (0 <= minimumIndex_2) ” 
  &&  “ (minimumIndex_2 <= maximumIndex_2) ” 
  &&  “ (maximumIndex_2 < heightSize_pre) ” 
  &&  “ (0 <= currentHeight_2) ” 
  &&  “ (currentHeight_2 <= 10000) ” 
  &&  “ (0 <= distanceToMinimum_2) ” 
  &&  “ (distanceToMinimum_2 <= 99999) ” 
  &&  “ (0 <= distanceToMaximum_2) ” 
  &&  “ (distanceToMaximum_2 <= 99999) ” 
  &&  “ (distanceToMinimum_2 = (index_2 - minimumIndex_2 )) ” 
  &&  “ (distanceToMaximum_2 = (index_2 - maximumIndex_2 )) ” 
  &&  “ (distanceToMinimum_2 <= width_2) ” 
  &&  “ (distanceToMaximum_2 <= width_2) ” 
  &&  “ (width_2 = distanceToMaximum_2) ” 
  &&  “ (0 <= width_2) ” 
  &&  “ (width_2 <= 99999) ” 
  &&  “ (0 <= maximumArea_2) ” 
  &&  “ (maximumArea_2 <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k_2 minimumIndex_2 maximumIndex_2 ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k_2 maximumArea_2 ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  ((( &( "distanceToMinimum" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "width" ) )) # Int  |-> distanceToMinimum_2)
  **  ((( &( "area" ) )) # Int  |-> (width_2 * currentHeight_2 ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  ((( &( "k" ) )) # Int  |-> k_2)
  **  ((( &( "index" ) )) # Int  |-> index_2)
  **  ((( &( "currentHeight" ) )) # Int  |-> currentHeight_2)
  **  ((( &( "minimumIndex" ) )) # Int  |-> minimumIndex_2)
  **  ((( &( "maximumIndex" ) )) # Int  |-> maximumIndex_2)
  **  ((( &( "distanceToMaximum" ) )) # Int  |-> distanceToMaximum_2)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea_2)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i ))
.

Definition maxAreaNLogN_entail_wit_9_1 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (distanceToMinimum = distanceToMinimum)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight ) <= INT_MAX)) (PreH10 : (distanceToMaximum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight ) >= INT_MIN)) (PreH18 : (index > maximumIndex)) (PreH19 : (index >= minimumIndex)) (PreH20 : ((width * currentHeight ) > maximumArea)) (PreH21 : (2 <= heightSize_pre)) (PreH22 : (heightSize_pre <= 100000)) (PreH23 : ((Zlength (l)) = heightSize_pre)) (PreH24 : (1 <= k)) (PreH25 : (k < heightSize_pre)) (PreH26 : (index = (Znth k sorted_i_2 0))) (PreH27 : (currentHeight = (Znth k sorted_h_2 0))) (PreH28 : (currentHeight = (Znth index l 0))) (PreH29 : (0 <= index)) (PreH30 : (index < heightSize_pre)) (PreH31 : (0 <= minimumIndex)) (PreH32 : (minimumIndex <= maximumIndex)) (PreH33 : (maximumIndex < heightSize_pre)) (PreH34 : (0 <= currentHeight)) (PreH35 : (currentHeight <= 10000)) (PreH36 : (0 <= distanceToMinimum)) (PreH37 : (distanceToMinimum <= 99999)) (PreH38 : (0 <= distanceToMaximum)) (PreH39 : (distanceToMaximum <= 99999)) (PreH40 : (distanceToMinimum = (index - minimumIndex ))) (PreH41 : (distanceToMaximum = (index - maximumIndex ))) (PreH42 : (distanceToMinimum <= width)) (PreH43 : (distanceToMaximum <= width)) (PreH44 : (width = distanceToMinimum)) (PreH45 : (0 <= width)) (PreH46 : (width <= 99999)) (PreH47 : (0 <= maximumArea)) (PreH48 : (maximumArea <= 999990000)) (PreH49 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH50 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH51 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH52 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= index) ” 
  &&  “ (index < heightSize_pre) ” 
  &&  “ (0 <= (width * currentHeight )) ” 
  &&  “ ((width * currentHeight ) <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) minimumIndex index ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) (width * currentHeight ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (distanceToMaximum <= INT_MAX)) (PreH2 : (maximumIndex <= INT_MAX)) (PreH3 : (minimumIndex <= INT_MAX)) (PreH4 : (currentHeight <= INT_MAX)) (PreH5 : (index <= INT_MAX)) (PreH6 : (k <= INT_MAX)) (PreH7 : (heightSize_pre <= INT_MAX)) (PreH8 : ((width * currentHeight ) <= INT_MAX)) (PreH9 : (distanceToMaximum >= INT_MIN)) (PreH10 : (maximumIndex >= INT_MIN)) (PreH11 : (minimumIndex >= INT_MIN)) (PreH12 : (currentHeight >= INT_MIN)) (PreH13 : (index >= INT_MIN)) (PreH14 : (k >= INT_MIN)) (PreH15 : (heightSize_pre >= INT_MIN)) (PreH16 : ((width * currentHeight ) >= INT_MIN)) (PreH17 : (index > maximumIndex)) (PreH18 : (index >= minimumIndex)) (PreH19 : ((width * currentHeight ) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 0))) (PreH26 : (currentHeight = (Znth k sorted_h_2 0))) (PreH27 : (currentHeight = (Znth index l 0))) (PreH28 : (0 <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : (0 <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : (0 <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : (0 <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : (0 <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (index - minimumIndex ))) (PreH40 : (distanceToMaximum = (index - maximumIndex ))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMinimum)) (PreH44 : (0 <= width)) (PreH45 : (width <= 99999)) (PreH46 : (0 <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH51 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMinimum * currentHeight ) ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex index ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_1_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (distanceToMaximum <= INT_MAX)) (PreH2 : (maximumIndex <= INT_MAX)) (PreH3 : (minimumIndex <= INT_MAX)) (PreH4 : (currentHeight <= INT_MAX)) (PreH5 : (index <= INT_MAX)) (PreH6 : (k <= INT_MAX)) (PreH7 : (heightSize_pre <= INT_MAX)) (PreH8 : ((width * currentHeight ) <= INT_MAX)) (PreH9 : (distanceToMaximum >= INT_MIN)) (PreH10 : (maximumIndex >= INT_MIN)) (PreH11 : (minimumIndex >= INT_MIN)) (PreH12 : (currentHeight >= INT_MIN)) (PreH13 : (index >= INT_MIN)) (PreH14 : (k >= INT_MIN)) (PreH15 : (heightSize_pre >= INT_MIN)) (PreH16 : ((width * currentHeight ) >= INT_MIN)) (PreH17 : (index > maximumIndex)) (PreH18 : (index >= minimumIndex)) (PreH19 : ((width * currentHeight ) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 0))) (PreH26 : (currentHeight = (Znth k sorted_h_2 0))) (PreH27 : (currentHeight = (Znth index l 0))) (PreH28 : (0 <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : (0 <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : (0 <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : (0 <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : (0 <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (index - minimumIndex ))) (PreH40 : (distanceToMaximum = (index - maximumIndex ))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMinimum)) (PreH44 : (0 <= width)) (PreH45 : (width <= 99999)) (PreH46 : (0 <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH51 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_1_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (distanceToMaximum <= INT_MAX)) (PreH2 : (maximumIndex <= INT_MAX)) (PreH3 : (minimumIndex <= INT_MAX)) (PreH4 : (currentHeight <= INT_MAX)) (PreH5 : (index <= INT_MAX)) (PreH6 : (k <= INT_MAX)) (PreH7 : (heightSize_pre <= INT_MAX)) (PreH8 : ((width * currentHeight ) <= INT_MAX)) (PreH9 : (distanceToMaximum >= INT_MIN)) (PreH10 : (maximumIndex >= INT_MIN)) (PreH11 : (minimumIndex >= INT_MIN)) (PreH12 : (currentHeight >= INT_MIN)) (PreH13 : (index >= INT_MIN)) (PreH14 : (k >= INT_MIN)) (PreH15 : (heightSize_pre >= INT_MIN)) (PreH16 : ((width * currentHeight ) >= INT_MIN)) (PreH17 : (index > maximumIndex)) (PreH18 : (index >= minimumIndex)) (PreH19 : ((width * currentHeight ) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 0))) (PreH26 : (currentHeight = (Znth k sorted_h_2 0))) (PreH27 : (currentHeight = (Znth index l 0))) (PreH28 : (0 <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : (0 <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : (0 <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : (0 <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : (0 <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (index - minimumIndex ))) (PreH40 : (distanceToMaximum = (index - maximumIndex ))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMinimum)) (PreH44 : (0 <= width)) (PreH45 : (width <= 99999)) (PreH46 : (0 <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH51 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMinimum * currentHeight ) )
.

Definition maxAreaNLogN_entail_wit_9_1_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (distanceToMaximum <= INT_MAX)) (PreH2 : (maximumIndex <= INT_MAX)) (PreH3 : (minimumIndex <= INT_MAX)) (PreH4 : (currentHeight <= INT_MAX)) (PreH5 : (index <= INT_MAX)) (PreH6 : (k <= INT_MAX)) (PreH7 : (heightSize_pre <= INT_MAX)) (PreH8 : ((width * currentHeight ) <= INT_MAX)) (PreH9 : (distanceToMaximum >= INT_MIN)) (PreH10 : (maximumIndex >= INT_MIN)) (PreH11 : (minimumIndex >= INT_MIN)) (PreH12 : (currentHeight >= INT_MIN)) (PreH13 : (index >= INT_MIN)) (PreH14 : (k >= INT_MIN)) (PreH15 : (heightSize_pre >= INT_MIN)) (PreH16 : ((width * currentHeight ) >= INT_MIN)) (PreH17 : (index > maximumIndex)) (PreH18 : (index >= minimumIndex)) (PreH19 : ((width * currentHeight ) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 0))) (PreH26 : (currentHeight = (Znth k sorted_h_2 0))) (PreH27 : (currentHeight = (Znth index l 0))) (PreH28 : (0 <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : (0 <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : (0 <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : (0 <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : (0 <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (index - minimumIndex ))) (PreH40 : (distanceToMaximum = (index - maximumIndex ))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMinimum)) (PreH44 : (0 <= width)) (PreH45 : (width <= 99999)) (PreH46 : (0 <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH51 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex index )
.

Definition maxAreaNLogN_entail_wit_9_2 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (distanceToMinimum = distanceToMinimum)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight ) <= INT_MAX)) (PreH10 : (distanceToMaximum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight ) >= INT_MIN)) (PreH18 : (index > maximumIndex)) (PreH19 : (index >= minimumIndex)) (PreH20 : ((width * currentHeight ) > maximumArea)) (PreH21 : (2 <= heightSize_pre)) (PreH22 : (heightSize_pre <= 100000)) (PreH23 : ((Zlength (l)) = heightSize_pre)) (PreH24 : (1 <= k)) (PreH25 : (k < heightSize_pre)) (PreH26 : (index = (Znth k sorted_i_2 0))) (PreH27 : (currentHeight = (Znth k sorted_h_2 0))) (PreH28 : (currentHeight = (Znth index l 0))) (PreH29 : (0 <= index)) (PreH30 : (index < heightSize_pre)) (PreH31 : (0 <= minimumIndex)) (PreH32 : (minimumIndex <= maximumIndex)) (PreH33 : (maximumIndex < heightSize_pre)) (PreH34 : (0 <= currentHeight)) (PreH35 : (currentHeight <= 10000)) (PreH36 : (0 <= distanceToMinimum)) (PreH37 : (distanceToMinimum <= 99999)) (PreH38 : (0 <= distanceToMaximum)) (PreH39 : (distanceToMaximum <= 99999)) (PreH40 : (distanceToMinimum = (index - minimumIndex ))) (PreH41 : (distanceToMaximum = (index - maximumIndex ))) (PreH42 : (distanceToMinimum <= width)) (PreH43 : (distanceToMaximum <= width)) (PreH44 : (width = distanceToMaximum)) (PreH45 : (0 <= width)) (PreH46 : (width <= 99999)) (PreH47 : (0 <= maximumArea)) (PreH48 : (maximumArea <= 999990000)) (PreH49 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH50 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH51 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH52 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= index) ” 
  &&  “ (index < heightSize_pre) ” 
  &&  “ (0 <= (width * currentHeight )) ” 
  &&  “ ((width * currentHeight ) <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) minimumIndex index ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) (width * currentHeight ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (distanceToMaximum <= INT_MAX)) (PreH2 : (maximumIndex <= INT_MAX)) (PreH3 : (minimumIndex <= INT_MAX)) (PreH4 : (currentHeight <= INT_MAX)) (PreH5 : (index <= INT_MAX)) (PreH6 : (k <= INT_MAX)) (PreH7 : (heightSize_pre <= INT_MAX)) (PreH8 : ((width * currentHeight ) <= INT_MAX)) (PreH9 : (distanceToMaximum >= INT_MIN)) (PreH10 : (maximumIndex >= INT_MIN)) (PreH11 : (minimumIndex >= INT_MIN)) (PreH12 : (currentHeight >= INT_MIN)) (PreH13 : (index >= INT_MIN)) (PreH14 : (k >= INT_MIN)) (PreH15 : (heightSize_pre >= INT_MIN)) (PreH16 : ((width * currentHeight ) >= INT_MIN)) (PreH17 : (index > maximumIndex)) (PreH18 : (index >= minimumIndex)) (PreH19 : ((width * currentHeight ) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 0))) (PreH26 : (currentHeight = (Znth k sorted_h_2 0))) (PreH27 : (currentHeight = (Znth index l 0))) (PreH28 : (0 <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : (0 <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : (0 <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : (0 <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : (0 <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (index - minimumIndex ))) (PreH40 : (distanceToMaximum = (index - maximumIndex ))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMaximum)) (PreH44 : (0 <= width)) (PreH45 : (width <= 99999)) (PreH46 : (0 <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH51 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMaximum * currentHeight ) ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex index ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_2_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (distanceToMaximum <= INT_MAX)) (PreH2 : (maximumIndex <= INT_MAX)) (PreH3 : (minimumIndex <= INT_MAX)) (PreH4 : (currentHeight <= INT_MAX)) (PreH5 : (index <= INT_MAX)) (PreH6 : (k <= INT_MAX)) (PreH7 : (heightSize_pre <= INT_MAX)) (PreH8 : ((width * currentHeight ) <= INT_MAX)) (PreH9 : (distanceToMaximum >= INT_MIN)) (PreH10 : (maximumIndex >= INT_MIN)) (PreH11 : (minimumIndex >= INT_MIN)) (PreH12 : (currentHeight >= INT_MIN)) (PreH13 : (index >= INT_MIN)) (PreH14 : (k >= INT_MIN)) (PreH15 : (heightSize_pre >= INT_MIN)) (PreH16 : ((width * currentHeight ) >= INT_MIN)) (PreH17 : (index > maximumIndex)) (PreH18 : (index >= minimumIndex)) (PreH19 : ((width * currentHeight ) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 0))) (PreH26 : (currentHeight = (Znth k sorted_h_2 0))) (PreH27 : (currentHeight = (Znth index l 0))) (PreH28 : (0 <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : (0 <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : (0 <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : (0 <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : (0 <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (index - minimumIndex ))) (PreH40 : (distanceToMaximum = (index - maximumIndex ))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMaximum)) (PreH44 : (0 <= width)) (PreH45 : (width <= 99999)) (PreH46 : (0 <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH51 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_2_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (distanceToMaximum <= INT_MAX)) (PreH2 : (maximumIndex <= INT_MAX)) (PreH3 : (minimumIndex <= INT_MAX)) (PreH4 : (currentHeight <= INT_MAX)) (PreH5 : (index <= INT_MAX)) (PreH6 : (k <= INT_MAX)) (PreH7 : (heightSize_pre <= INT_MAX)) (PreH8 : ((width * currentHeight ) <= INT_MAX)) (PreH9 : (distanceToMaximum >= INT_MIN)) (PreH10 : (maximumIndex >= INT_MIN)) (PreH11 : (minimumIndex >= INT_MIN)) (PreH12 : (currentHeight >= INT_MIN)) (PreH13 : (index >= INT_MIN)) (PreH14 : (k >= INT_MIN)) (PreH15 : (heightSize_pre >= INT_MIN)) (PreH16 : ((width * currentHeight ) >= INT_MIN)) (PreH17 : (index > maximumIndex)) (PreH18 : (index >= minimumIndex)) (PreH19 : ((width * currentHeight ) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 0))) (PreH26 : (currentHeight = (Znth k sorted_h_2 0))) (PreH27 : (currentHeight = (Znth index l 0))) (PreH28 : (0 <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : (0 <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : (0 <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : (0 <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : (0 <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (index - minimumIndex ))) (PreH40 : (distanceToMaximum = (index - maximumIndex ))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMaximum)) (PreH44 : (0 <= width)) (PreH45 : (width <= 99999)) (PreH46 : (0 <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH51 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMaximum * currentHeight ) )
.

Definition maxAreaNLogN_entail_wit_9_2_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (distanceToMaximum <= INT_MAX)) (PreH2 : (maximumIndex <= INT_MAX)) (PreH3 : (minimumIndex <= INT_MAX)) (PreH4 : (currentHeight <= INT_MAX)) (PreH5 : (index <= INT_MAX)) (PreH6 : (k <= INT_MAX)) (PreH7 : (heightSize_pre <= INT_MAX)) (PreH8 : ((width * currentHeight ) <= INT_MAX)) (PreH9 : (distanceToMaximum >= INT_MIN)) (PreH10 : (maximumIndex >= INT_MIN)) (PreH11 : (minimumIndex >= INT_MIN)) (PreH12 : (currentHeight >= INT_MIN)) (PreH13 : (index >= INT_MIN)) (PreH14 : (k >= INT_MIN)) (PreH15 : (heightSize_pre >= INT_MIN)) (PreH16 : ((width * currentHeight ) >= INT_MIN)) (PreH17 : (index > maximumIndex)) (PreH18 : (index >= minimumIndex)) (PreH19 : ((width * currentHeight ) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 0))) (PreH26 : (currentHeight = (Znth k sorted_h_2 0))) (PreH27 : (currentHeight = (Znth index l 0))) (PreH28 : (0 <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : (0 <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : (0 <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : (0 <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : (0 <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (index - minimumIndex ))) (PreH40 : (distanceToMaximum = (index - maximumIndex ))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMaximum)) (PreH44 : (0 <= width)) (PreH45 : (width <= 99999)) (PreH46 : (0 <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH51 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex index )
.

Definition maxAreaNLogN_entail_wit_9_3 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (distanceToMinimum = distanceToMinimum)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMaximum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight ) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMaximum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight ) >= INT_MIN)) (PreH20 : (index > maximumIndex)) (PreH21 : (index >= minimumIndex)) (PreH22 : ((width * currentHeight ) <= maximumArea)) (PreH23 : (2 <= heightSize_pre)) (PreH24 : (heightSize_pre <= 100000)) (PreH25 : ((Zlength (l)) = heightSize_pre)) (PreH26 : (1 <= k)) (PreH27 : (k < heightSize_pre)) (PreH28 : (index = (Znth k sorted_i_2 0))) (PreH29 : (currentHeight = (Znth k sorted_h_2 0))) (PreH30 : (currentHeight = (Znth index l 0))) (PreH31 : (0 <= index)) (PreH32 : (index < heightSize_pre)) (PreH33 : (0 <= minimumIndex)) (PreH34 : (minimumIndex <= maximumIndex)) (PreH35 : (maximumIndex < heightSize_pre)) (PreH36 : (0 <= currentHeight)) (PreH37 : (currentHeight <= 10000)) (PreH38 : (0 <= distanceToMinimum)) (PreH39 : (distanceToMinimum <= 99999)) (PreH40 : (0 <= distanceToMaximum)) (PreH41 : (distanceToMaximum <= 99999)) (PreH42 : (distanceToMinimum = (index - minimumIndex ))) (PreH43 : (distanceToMaximum = (index - maximumIndex ))) (PreH44 : (distanceToMinimum <= width)) (PreH45 : (distanceToMaximum <= width)) (PreH46 : (width = distanceToMinimum)) (PreH47 : (0 <= width)) (PreH48 : (width <= 99999)) (PreH49 : (0 <= maximumArea)) (PreH50 : (maximumArea <= 999990000)) (PreH51 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH52 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH53 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH54 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= index) ” 
  &&  “ (index < heightSize_pre) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) minimumIndex index ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (maximumArea <= INT_MAX)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight ) <= INT_MAX)) (PreH10 : (maximumArea >= INT_MIN)) (PreH11 : (distanceToMaximum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight ) >= INT_MIN)) (PreH19 : (index > maximumIndex)) (PreH20 : (index >= minimumIndex)) (PreH21 : ((width * currentHeight ) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 0))) (PreH28 : (currentHeight = (Znth k sorted_h_2 0))) (PreH29 : (currentHeight = (Znth index l 0))) (PreH30 : (0 <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : (0 <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : (0 <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : (0 <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : (0 <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (index - minimumIndex ))) (PreH42 : (distanceToMaximum = (index - maximumIndex ))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMinimum)) (PreH46 : (0 <= width)) (PreH47 : (width <= 99999)) (PreH48 : (0 <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH53 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex index ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_3_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (maximumArea <= INT_MAX)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight ) <= INT_MAX)) (PreH10 : (maximumArea >= INT_MIN)) (PreH11 : (distanceToMaximum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight ) >= INT_MIN)) (PreH19 : (index > maximumIndex)) (PreH20 : (index >= minimumIndex)) (PreH21 : ((width * currentHeight ) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 0))) (PreH28 : (currentHeight = (Znth k sorted_h_2 0))) (PreH29 : (currentHeight = (Znth index l 0))) (PreH30 : (0 <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : (0 <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : (0 <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : (0 <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : (0 <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (index - minimumIndex ))) (PreH42 : (distanceToMaximum = (index - maximumIndex ))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMinimum)) (PreH46 : (0 <= width)) (PreH47 : (width <= 99999)) (PreH48 : (0 <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH53 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_3_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (maximumArea <= INT_MAX)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight ) <= INT_MAX)) (PreH10 : (maximumArea >= INT_MIN)) (PreH11 : (distanceToMaximum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight ) >= INT_MIN)) (PreH19 : (index > maximumIndex)) (PreH20 : (index >= minimumIndex)) (PreH21 : ((width * currentHeight ) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 0))) (PreH28 : (currentHeight = (Znth k sorted_h_2 0))) (PreH29 : (currentHeight = (Znth index l 0))) (PreH30 : (0 <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : (0 <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : (0 <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : (0 <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : (0 <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (index - minimumIndex ))) (PreH42 : (distanceToMaximum = (index - maximumIndex ))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMinimum)) (PreH46 : (0 <= width)) (PreH47 : (width <= 99999)) (PreH48 : (0 <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH53 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea )
.

Definition maxAreaNLogN_entail_wit_9_3_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (maximumArea <= INT_MAX)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight ) <= INT_MAX)) (PreH10 : (maximumArea >= INT_MIN)) (PreH11 : (distanceToMaximum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight ) >= INT_MIN)) (PreH19 : (index > maximumIndex)) (PreH20 : (index >= minimumIndex)) (PreH21 : ((width * currentHeight ) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 0))) (PreH28 : (currentHeight = (Znth k sorted_h_2 0))) (PreH29 : (currentHeight = (Znth index l 0))) (PreH30 : (0 <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : (0 <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : (0 <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : (0 <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : (0 <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (index - minimumIndex ))) (PreH42 : (distanceToMaximum = (index - maximumIndex ))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMinimum)) (PreH46 : (0 <= width)) (PreH47 : (width <= 99999)) (PreH48 : (0 <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH53 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex index )
.

Definition maxAreaNLogN_entail_wit_9_4 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (distanceToMinimum = distanceToMinimum)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMaximum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight ) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMaximum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight ) >= INT_MIN)) (PreH20 : (index > maximumIndex)) (PreH21 : (index >= minimumIndex)) (PreH22 : ((width * currentHeight ) <= maximumArea)) (PreH23 : (2 <= heightSize_pre)) (PreH24 : (heightSize_pre <= 100000)) (PreH25 : ((Zlength (l)) = heightSize_pre)) (PreH26 : (1 <= k)) (PreH27 : (k < heightSize_pre)) (PreH28 : (index = (Znth k sorted_i_2 0))) (PreH29 : (currentHeight = (Znth k sorted_h_2 0))) (PreH30 : (currentHeight = (Znth index l 0))) (PreH31 : (0 <= index)) (PreH32 : (index < heightSize_pre)) (PreH33 : (0 <= minimumIndex)) (PreH34 : (minimumIndex <= maximumIndex)) (PreH35 : (maximumIndex < heightSize_pre)) (PreH36 : (0 <= currentHeight)) (PreH37 : (currentHeight <= 10000)) (PreH38 : (0 <= distanceToMinimum)) (PreH39 : (distanceToMinimum <= 99999)) (PreH40 : (0 <= distanceToMaximum)) (PreH41 : (distanceToMaximum <= 99999)) (PreH42 : (distanceToMinimum = (index - minimumIndex ))) (PreH43 : (distanceToMaximum = (index - maximumIndex ))) (PreH44 : (distanceToMinimum <= width)) (PreH45 : (distanceToMaximum <= width)) (PreH46 : (width = distanceToMaximum)) (PreH47 : (0 <= width)) (PreH48 : (width <= 99999)) (PreH49 : (0 <= maximumArea)) (PreH50 : (maximumArea <= 999990000)) (PreH51 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH52 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH53 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH54 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= index) ” 
  &&  “ (index < heightSize_pre) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) minimumIndex index ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (maximumArea <= INT_MAX)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight ) <= INT_MAX)) (PreH10 : (maximumArea >= INT_MIN)) (PreH11 : (distanceToMaximum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight ) >= INT_MIN)) (PreH19 : (index > maximumIndex)) (PreH20 : (index >= minimumIndex)) (PreH21 : ((width * currentHeight ) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 0))) (PreH28 : (currentHeight = (Znth k sorted_h_2 0))) (PreH29 : (currentHeight = (Znth index l 0))) (PreH30 : (0 <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : (0 <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : (0 <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : (0 <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : (0 <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (index - minimumIndex ))) (PreH42 : (distanceToMaximum = (index - maximumIndex ))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMaximum)) (PreH46 : (0 <= width)) (PreH47 : (width <= 99999)) (PreH48 : (0 <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH53 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex index ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_4_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (maximumArea <= INT_MAX)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight ) <= INT_MAX)) (PreH10 : (maximumArea >= INT_MIN)) (PreH11 : (distanceToMaximum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight ) >= INT_MIN)) (PreH19 : (index > maximumIndex)) (PreH20 : (index >= minimumIndex)) (PreH21 : ((width * currentHeight ) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 0))) (PreH28 : (currentHeight = (Znth k sorted_h_2 0))) (PreH29 : (currentHeight = (Znth index l 0))) (PreH30 : (0 <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : (0 <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : (0 <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : (0 <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : (0 <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (index - minimumIndex ))) (PreH42 : (distanceToMaximum = (index - maximumIndex ))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMaximum)) (PreH46 : (0 <= width)) (PreH47 : (width <= 99999)) (PreH48 : (0 <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH53 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_4_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (maximumArea <= INT_MAX)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight ) <= INT_MAX)) (PreH10 : (maximumArea >= INT_MIN)) (PreH11 : (distanceToMaximum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight ) >= INT_MIN)) (PreH19 : (index > maximumIndex)) (PreH20 : (index >= minimumIndex)) (PreH21 : ((width * currentHeight ) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 0))) (PreH28 : (currentHeight = (Znth k sorted_h_2 0))) (PreH29 : (currentHeight = (Znth index l 0))) (PreH30 : (0 <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : (0 <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : (0 <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : (0 <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : (0 <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (index - minimumIndex ))) (PreH42 : (distanceToMaximum = (index - maximumIndex ))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMaximum)) (PreH46 : (0 <= width)) (PreH47 : (width <= 99999)) (PreH48 : (0 <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH53 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea )
.

Definition maxAreaNLogN_entail_wit_9_4_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (maximumArea <= INT_MAX)) (PreH2 : (distanceToMaximum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight ) <= INT_MAX)) (PreH10 : (maximumArea >= INT_MIN)) (PreH11 : (distanceToMaximum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight ) >= INT_MIN)) (PreH19 : (index > maximumIndex)) (PreH20 : (index >= minimumIndex)) (PreH21 : ((width * currentHeight ) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 0))) (PreH28 : (currentHeight = (Znth k sorted_h_2 0))) (PreH29 : (currentHeight = (Znth index l 0))) (PreH30 : (0 <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : (0 <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : (0 <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : (0 <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : (0 <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (index - minimumIndex ))) (PreH42 : (distanceToMaximum = (index - maximumIndex ))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMaximum)) (PreH46 : (0 <= width)) (PreH47 : (width <= 99999)) (PreH48 : (0 <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH53 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex index )
.

Definition maxAreaNLogN_entail_wit_9_5 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight ) <= INT_MAX)) (PreH11 : (distanceToMinimum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight ) >= INT_MIN)) (PreH19 : (index < minimumIndex)) (PreH20 : ((width * currentHeight ) > maximumArea)) (PreH21 : (2 <= heightSize_pre)) (PreH22 : (heightSize_pre <= 100000)) (PreH23 : ((Zlength (l)) = heightSize_pre)) (PreH24 : (1 <= k)) (PreH25 : (k < heightSize_pre)) (PreH26 : (index = (Znth k sorted_i_2 0))) (PreH27 : (currentHeight = (Znth k sorted_h_2 0))) (PreH28 : (currentHeight = (Znth index l 0))) (PreH29 : (0 <= index)) (PreH30 : (index < heightSize_pre)) (PreH31 : (0 <= minimumIndex)) (PreH32 : (minimumIndex <= maximumIndex)) (PreH33 : (maximumIndex < heightSize_pre)) (PreH34 : (0 <= currentHeight)) (PreH35 : (currentHeight <= 10000)) (PreH36 : (0 <= distanceToMinimum)) (PreH37 : (distanceToMinimum <= 99999)) (PreH38 : (0 <= distanceToMaximum)) (PreH39 : (distanceToMaximum <= 99999)) (PreH40 : (distanceToMinimum = (minimumIndex - index ))) (PreH41 : (distanceToMaximum = (maximumIndex - index ))) (PreH42 : (distanceToMinimum <= width)) (PreH43 : (distanceToMaximum <= width)) (PreH44 : (width = distanceToMinimum)) (PreH45 : (0 <= width)) (PreH46 : (width <= 99999)) (PreH47 : (0 <= maximumArea)) (PreH48 : (maximumArea <= 999990000)) (PreH49 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH50 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH51 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH52 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (width * currentHeight )) ” 
  &&  “ ((width * currentHeight ) <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) index maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) (width * currentHeight ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMinimum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight ) <= INT_MAX)) (PreH10 : (distanceToMinimum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight ) >= INT_MIN)) (PreH18 : (index < minimumIndex)) (PreH19 : ((width * currentHeight ) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 0))) (PreH26 : (currentHeight = (Znth k sorted_h_2 0))) (PreH27 : (currentHeight = (Znth index l 0))) (PreH28 : (0 <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : (0 <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : (0 <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : (0 <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : (0 <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (minimumIndex - index ))) (PreH40 : (distanceToMaximum = (maximumIndex - index ))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMinimum)) (PreH44 : (0 <= width)) (PreH45 : (width <= 99999)) (PreH46 : (0 <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH51 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMinimum * currentHeight ) ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) index maximumIndex ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_5_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMinimum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight ) <= INT_MAX)) (PreH10 : (distanceToMinimum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight ) >= INT_MIN)) (PreH18 : (index < minimumIndex)) (PreH19 : ((width * currentHeight ) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 0))) (PreH26 : (currentHeight = (Znth k sorted_h_2 0))) (PreH27 : (currentHeight = (Znth index l 0))) (PreH28 : (0 <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : (0 <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : (0 <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : (0 <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : (0 <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (minimumIndex - index ))) (PreH40 : (distanceToMaximum = (maximumIndex - index ))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMinimum)) (PreH44 : (0 <= width)) (PreH45 : (width <= 99999)) (PreH46 : (0 <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH51 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_5_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMinimum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight ) <= INT_MAX)) (PreH10 : (distanceToMinimum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight ) >= INT_MIN)) (PreH18 : (index < minimumIndex)) (PreH19 : ((width * currentHeight ) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 0))) (PreH26 : (currentHeight = (Znth k sorted_h_2 0))) (PreH27 : (currentHeight = (Znth index l 0))) (PreH28 : (0 <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : (0 <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : (0 <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : (0 <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : (0 <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (minimumIndex - index ))) (PreH40 : (distanceToMaximum = (maximumIndex - index ))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMinimum)) (PreH44 : (0 <= width)) (PreH45 : (width <= 99999)) (PreH46 : (0 <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH51 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMinimum * currentHeight ) )
.

Definition maxAreaNLogN_entail_wit_9_5_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMinimum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight ) <= INT_MAX)) (PreH10 : (distanceToMinimum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight ) >= INT_MIN)) (PreH18 : (index < minimumIndex)) (PreH19 : ((width * currentHeight ) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 0))) (PreH26 : (currentHeight = (Znth k sorted_h_2 0))) (PreH27 : (currentHeight = (Znth index l 0))) (PreH28 : (0 <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : (0 <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : (0 <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : (0 <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : (0 <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (minimumIndex - index ))) (PreH40 : (distanceToMaximum = (maximumIndex - index ))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMinimum)) (PreH44 : (0 <= width)) (PreH45 : (width <= 99999)) (PreH46 : (0 <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH51 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) index maximumIndex )
.

Definition maxAreaNLogN_entail_wit_9_6 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight ) <= INT_MAX)) (PreH11 : (distanceToMinimum >= INT_MIN)) (PreH12 : (maximumIndex >= INT_MIN)) (PreH13 : (minimumIndex >= INT_MIN)) (PreH14 : (currentHeight >= INT_MIN)) (PreH15 : (index >= INT_MIN)) (PreH16 : (k >= INT_MIN)) (PreH17 : (heightSize_pre >= INT_MIN)) (PreH18 : ((width * currentHeight ) >= INT_MIN)) (PreH19 : (index < minimumIndex)) (PreH20 : ((width * currentHeight ) > maximumArea)) (PreH21 : (2 <= heightSize_pre)) (PreH22 : (heightSize_pre <= 100000)) (PreH23 : ((Zlength (l)) = heightSize_pre)) (PreH24 : (1 <= k)) (PreH25 : (k < heightSize_pre)) (PreH26 : (index = (Znth k sorted_i_2 0))) (PreH27 : (currentHeight = (Znth k sorted_h_2 0))) (PreH28 : (currentHeight = (Znth index l 0))) (PreH29 : (0 <= index)) (PreH30 : (index < heightSize_pre)) (PreH31 : (0 <= minimumIndex)) (PreH32 : (minimumIndex <= maximumIndex)) (PreH33 : (maximumIndex < heightSize_pre)) (PreH34 : (0 <= currentHeight)) (PreH35 : (currentHeight <= 10000)) (PreH36 : (0 <= distanceToMinimum)) (PreH37 : (distanceToMinimum <= 99999)) (PreH38 : (0 <= distanceToMaximum)) (PreH39 : (distanceToMaximum <= 99999)) (PreH40 : (distanceToMinimum = (minimumIndex - index ))) (PreH41 : (distanceToMaximum = (maximumIndex - index ))) (PreH42 : (distanceToMinimum <= width)) (PreH43 : (distanceToMaximum <= width)) (PreH44 : (width = distanceToMaximum)) (PreH45 : (0 <= width)) (PreH46 : (width <= 99999)) (PreH47 : (0 <= maximumArea)) (PreH48 : (maximumArea <= 999990000)) (PreH49 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH50 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH51 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH52 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (width * currentHeight )) ” 
  &&  “ ((width * currentHeight ) <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) index maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) (width * currentHeight ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMinimum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight ) <= INT_MAX)) (PreH10 : (distanceToMinimum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight ) >= INT_MIN)) (PreH18 : (index < minimumIndex)) (PreH19 : ((width * currentHeight ) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 0))) (PreH26 : (currentHeight = (Znth k sorted_h_2 0))) (PreH27 : (currentHeight = (Znth index l 0))) (PreH28 : (0 <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : (0 <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : (0 <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : (0 <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : (0 <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (minimumIndex - index ))) (PreH40 : (distanceToMaximum = (maximumIndex - index ))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMaximum)) (PreH44 : (0 <= width)) (PreH45 : (width <= 99999)) (PreH46 : (0 <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH51 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMaximum * currentHeight ) ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) index maximumIndex ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_6_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMinimum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight ) <= INT_MAX)) (PreH10 : (distanceToMinimum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight ) >= INT_MIN)) (PreH18 : (index < minimumIndex)) (PreH19 : ((width * currentHeight ) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 0))) (PreH26 : (currentHeight = (Znth k sorted_h_2 0))) (PreH27 : (currentHeight = (Znth index l 0))) (PreH28 : (0 <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : (0 <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : (0 <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : (0 <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : (0 <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (minimumIndex - index ))) (PreH40 : (distanceToMaximum = (maximumIndex - index ))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMaximum)) (PreH44 : (0 <= width)) (PreH45 : (width <= 99999)) (PreH46 : (0 <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH51 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_6_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMinimum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight ) <= INT_MAX)) (PreH10 : (distanceToMinimum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight ) >= INT_MIN)) (PreH18 : (index < minimumIndex)) (PreH19 : ((width * currentHeight ) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 0))) (PreH26 : (currentHeight = (Znth k sorted_h_2 0))) (PreH27 : (currentHeight = (Znth index l 0))) (PreH28 : (0 <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : (0 <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : (0 <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : (0 <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : (0 <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (minimumIndex - index ))) (PreH40 : (distanceToMaximum = (maximumIndex - index ))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMaximum)) (PreH44 : (0 <= width)) (PreH45 : (width <= 99999)) (PreH46 : (0 <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH51 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMaximum * currentHeight ) )
.

Definition maxAreaNLogN_entail_wit_9_6_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMinimum <= INT_MAX)) (PreH3 : (maximumIndex <= INT_MAX)) (PreH4 : (minimumIndex <= INT_MAX)) (PreH5 : (currentHeight <= INT_MAX)) (PreH6 : (index <= INT_MAX)) (PreH7 : (k <= INT_MAX)) (PreH8 : (heightSize_pre <= INT_MAX)) (PreH9 : ((width * currentHeight ) <= INT_MAX)) (PreH10 : (distanceToMinimum >= INT_MIN)) (PreH11 : (maximumIndex >= INT_MIN)) (PreH12 : (minimumIndex >= INT_MIN)) (PreH13 : (currentHeight >= INT_MIN)) (PreH14 : (index >= INT_MIN)) (PreH15 : (k >= INT_MIN)) (PreH16 : (heightSize_pre >= INT_MIN)) (PreH17 : ((width * currentHeight ) >= INT_MIN)) (PreH18 : (index < minimumIndex)) (PreH19 : ((width * currentHeight ) > maximumArea)) (PreH20 : (2 <= heightSize_pre)) (PreH21 : (heightSize_pre <= 100000)) (PreH22 : ((Zlength (l)) = heightSize_pre)) (PreH23 : (1 <= k)) (PreH24 : (k < heightSize_pre)) (PreH25 : (index = (Znth k sorted_i_2 0))) (PreH26 : (currentHeight = (Znth k sorted_h_2 0))) (PreH27 : (currentHeight = (Znth index l 0))) (PreH28 : (0 <= index)) (PreH29 : (index < heightSize_pre)) (PreH30 : (0 <= minimumIndex)) (PreH31 : (minimumIndex <= maximumIndex)) (PreH32 : (maximumIndex < heightSize_pre)) (PreH33 : (0 <= currentHeight)) (PreH34 : (currentHeight <= 10000)) (PreH35 : (0 <= distanceToMinimum)) (PreH36 : (distanceToMinimum <= 99999)) (PreH37 : (0 <= distanceToMaximum)) (PreH38 : (distanceToMaximum <= 99999)) (PreH39 : (distanceToMinimum = (minimumIndex - index ))) (PreH40 : (distanceToMaximum = (maximumIndex - index ))) (PreH41 : (distanceToMinimum <= width)) (PreH42 : (distanceToMaximum <= width)) (PreH43 : (width = distanceToMaximum)) (PreH44 : (0 <= width)) (PreH45 : (width <= 99999)) (PreH46 : (0 <= maximumArea)) (PreH47 : (maximumArea <= 999990000)) (PreH48 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH49 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH50 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH51 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) index maximumIndex )
.

Definition maxAreaNLogN_entail_wit_9_7 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (maximumArea <= INT_MAX)) (PreH4 : (distanceToMinimum <= INT_MAX)) (PreH5 : (maximumIndex <= INT_MAX)) (PreH6 : (minimumIndex <= INT_MAX)) (PreH7 : (currentHeight <= INT_MAX)) (PreH8 : (index <= INT_MAX)) (PreH9 : (k <= INT_MAX)) (PreH10 : (heightSize_pre <= INT_MAX)) (PreH11 : ((width * currentHeight ) <= INT_MAX)) (PreH12 : (maximumArea >= INT_MIN)) (PreH13 : (distanceToMinimum >= INT_MIN)) (PreH14 : (maximumIndex >= INT_MIN)) (PreH15 : (minimumIndex >= INT_MIN)) (PreH16 : (currentHeight >= INT_MIN)) (PreH17 : (index >= INT_MIN)) (PreH18 : (k >= INT_MIN)) (PreH19 : (heightSize_pre >= INT_MIN)) (PreH20 : ((width * currentHeight ) >= INT_MIN)) (PreH21 : (index < minimumIndex)) (PreH22 : ((width * currentHeight ) <= maximumArea)) (PreH23 : (2 <= heightSize_pre)) (PreH24 : (heightSize_pre <= 100000)) (PreH25 : ((Zlength (l)) = heightSize_pre)) (PreH26 : (1 <= k)) (PreH27 : (k < heightSize_pre)) (PreH28 : (index = (Znth k sorted_i_2 0))) (PreH29 : (currentHeight = (Znth k sorted_h_2 0))) (PreH30 : (currentHeight = (Znth index l 0))) (PreH31 : (0 <= index)) (PreH32 : (index < heightSize_pre)) (PreH33 : (0 <= minimumIndex)) (PreH34 : (minimumIndex <= maximumIndex)) (PreH35 : (maximumIndex < heightSize_pre)) (PreH36 : (0 <= currentHeight)) (PreH37 : (currentHeight <= 10000)) (PreH38 : (0 <= distanceToMinimum)) (PreH39 : (distanceToMinimum <= 99999)) (PreH40 : (0 <= distanceToMaximum)) (PreH41 : (distanceToMaximum <= 99999)) (PreH42 : (distanceToMinimum = (minimumIndex - index ))) (PreH43 : (distanceToMaximum = (maximumIndex - index ))) (PreH44 : (distanceToMinimum <= width)) (PreH45 : (distanceToMaximum <= width)) (PreH46 : (width = distanceToMinimum)) (PreH47 : (0 <= width)) (PreH48 : (width <= 99999)) (PreH49 : (0 <= maximumArea)) (PreH50 : (maximumArea <= 999990000)) (PreH51 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH52 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH53 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH54 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) index maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight ) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMinimum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight ) >= INT_MIN)) (PreH20 : (index < minimumIndex)) (PreH21 : ((width * currentHeight ) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 0))) (PreH28 : (currentHeight = (Znth k sorted_h_2 0))) (PreH29 : (currentHeight = (Znth index l 0))) (PreH30 : (0 <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : (0 <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : (0 <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : (0 <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : (0 <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (minimumIndex - index ))) (PreH42 : (distanceToMaximum = (maximumIndex - index ))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMinimum)) (PreH46 : (0 <= width)) (PreH47 : (width <= 99999)) (PreH48 : (0 <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH53 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) index maximumIndex ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_7_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight ) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMinimum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight ) >= INT_MIN)) (PreH20 : (index < minimumIndex)) (PreH21 : ((width * currentHeight ) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 0))) (PreH28 : (currentHeight = (Znth k sorted_h_2 0))) (PreH29 : (currentHeight = (Znth index l 0))) (PreH30 : (0 <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : (0 <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : (0 <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : (0 <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : (0 <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (minimumIndex - index ))) (PreH42 : (distanceToMaximum = (maximumIndex - index ))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMinimum)) (PreH46 : (0 <= width)) (PreH47 : (width <= 99999)) (PreH48 : (0 <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH53 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_7_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight ) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMinimum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight ) >= INT_MIN)) (PreH20 : (index < minimumIndex)) (PreH21 : ((width * currentHeight ) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 0))) (PreH28 : (currentHeight = (Znth k sorted_h_2 0))) (PreH29 : (currentHeight = (Znth index l 0))) (PreH30 : (0 <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : (0 <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : (0 <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : (0 <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : (0 <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (minimumIndex - index ))) (PreH42 : (distanceToMaximum = (maximumIndex - index ))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMinimum)) (PreH46 : (0 <= width)) (PreH47 : (width <= 99999)) (PreH48 : (0 <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH53 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea )
.

Definition maxAreaNLogN_entail_wit_9_7_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight ) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMinimum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight ) >= INT_MIN)) (PreH20 : (index < minimumIndex)) (PreH21 : ((width * currentHeight ) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 0))) (PreH28 : (currentHeight = (Znth k sorted_h_2 0))) (PreH29 : (currentHeight = (Znth index l 0))) (PreH30 : (0 <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : (0 <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : (0 <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : (0 <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : (0 <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (minimumIndex - index ))) (PreH42 : (distanceToMaximum = (maximumIndex - index ))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMinimum)) (PreH46 : (0 <= width)) (PreH47 : (width <= 99999)) (PreH48 : (0 <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH53 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) index maximumIndex )
.

Definition maxAreaNLogN_entail_wit_9_8 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (distanceToMaximum = distanceToMaximum)) (PreH3 : (maximumArea <= INT_MAX)) (PreH4 : (distanceToMinimum <= INT_MAX)) (PreH5 : (maximumIndex <= INT_MAX)) (PreH6 : (minimumIndex <= INT_MAX)) (PreH7 : (currentHeight <= INT_MAX)) (PreH8 : (index <= INT_MAX)) (PreH9 : (k <= INT_MAX)) (PreH10 : (heightSize_pre <= INT_MAX)) (PreH11 : ((width * currentHeight ) <= INT_MAX)) (PreH12 : (maximumArea >= INT_MIN)) (PreH13 : (distanceToMinimum >= INT_MIN)) (PreH14 : (maximumIndex >= INT_MIN)) (PreH15 : (minimumIndex >= INT_MIN)) (PreH16 : (currentHeight >= INT_MIN)) (PreH17 : (index >= INT_MIN)) (PreH18 : (k >= INT_MIN)) (PreH19 : (heightSize_pre >= INT_MIN)) (PreH20 : ((width * currentHeight ) >= INT_MIN)) (PreH21 : (index < minimumIndex)) (PreH22 : ((width * currentHeight ) <= maximumArea)) (PreH23 : (2 <= heightSize_pre)) (PreH24 : (heightSize_pre <= 100000)) (PreH25 : ((Zlength (l)) = heightSize_pre)) (PreH26 : (1 <= k)) (PreH27 : (k < heightSize_pre)) (PreH28 : (index = (Znth k sorted_i_2 0))) (PreH29 : (currentHeight = (Znth k sorted_h_2 0))) (PreH30 : (currentHeight = (Znth index l 0))) (PreH31 : (0 <= index)) (PreH32 : (index < heightSize_pre)) (PreH33 : (0 <= minimumIndex)) (PreH34 : (minimumIndex <= maximumIndex)) (PreH35 : (maximumIndex < heightSize_pre)) (PreH36 : (0 <= currentHeight)) (PreH37 : (currentHeight <= 10000)) (PreH38 : (0 <= distanceToMinimum)) (PreH39 : (distanceToMinimum <= 99999)) (PreH40 : (0 <= distanceToMaximum)) (PreH41 : (distanceToMaximum <= 99999)) (PreH42 : (distanceToMinimum = (minimumIndex - index ))) (PreH43 : (distanceToMaximum = (maximumIndex - index ))) (PreH44 : (distanceToMinimum <= width)) (PreH45 : (distanceToMaximum <= width)) (PreH46 : (width = distanceToMaximum)) (PreH47 : (0 <= width)) (PreH48 : (width <= 99999)) (PreH49 : (0 <= maximumArea)) (PreH50 : (maximumArea <= 999990000)) (PreH51 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH52 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH53 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH54 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) index maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight ) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMinimum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight ) >= INT_MIN)) (PreH20 : (index < minimumIndex)) (PreH21 : ((width * currentHeight ) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 0))) (PreH28 : (currentHeight = (Znth k sorted_h_2 0))) (PreH29 : (currentHeight = (Znth index l 0))) (PreH30 : (0 <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : (0 <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : (0 <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : (0 <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : (0 <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (minimumIndex - index ))) (PreH42 : (distanceToMaximum = (maximumIndex - index ))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMaximum)) (PreH46 : (0 <= width)) (PreH47 : (width <= 99999)) (PreH48 : (0 <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH53 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) index maximumIndex ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_8_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight ) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMinimum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight ) >= INT_MIN)) (PreH20 : (index < minimumIndex)) (PreH21 : ((width * currentHeight ) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 0))) (PreH28 : (currentHeight = (Znth k sorted_h_2 0))) (PreH29 : (currentHeight = (Znth index l 0))) (PreH30 : (0 <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : (0 <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : (0 <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : (0 <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : (0 <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (minimumIndex - index ))) (PreH42 : (distanceToMaximum = (maximumIndex - index ))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMaximum)) (PreH46 : (0 <= width)) (PreH47 : (width <= 99999)) (PreH48 : (0 <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH53 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_8_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight ) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMinimum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight ) >= INT_MIN)) (PreH20 : (index < minimumIndex)) (PreH21 : ((width * currentHeight ) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 0))) (PreH28 : (currentHeight = (Znth k sorted_h_2 0))) (PreH29 : (currentHeight = (Znth index l 0))) (PreH30 : (0 <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : (0 <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : (0 <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : (0 <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : (0 <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (minimumIndex - index ))) (PreH42 : (distanceToMaximum = (maximumIndex - index ))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMaximum)) (PreH46 : (0 <= width)) (PreH47 : (width <= 99999)) (PreH48 : (0 <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH53 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea )
.

Definition maxAreaNLogN_entail_wit_9_8_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (maximumArea <= INT_MAX)) (PreH3 : (distanceToMinimum <= INT_MAX)) (PreH4 : (maximumIndex <= INT_MAX)) (PreH5 : (minimumIndex <= INT_MAX)) (PreH6 : (currentHeight <= INT_MAX)) (PreH7 : (index <= INT_MAX)) (PreH8 : (k <= INT_MAX)) (PreH9 : (heightSize_pre <= INT_MAX)) (PreH10 : ((width * currentHeight ) <= INT_MAX)) (PreH11 : (maximumArea >= INT_MIN)) (PreH12 : (distanceToMinimum >= INT_MIN)) (PreH13 : (maximumIndex >= INT_MIN)) (PreH14 : (minimumIndex >= INT_MIN)) (PreH15 : (currentHeight >= INT_MIN)) (PreH16 : (index >= INT_MIN)) (PreH17 : (k >= INT_MIN)) (PreH18 : (heightSize_pre >= INT_MIN)) (PreH19 : ((width * currentHeight ) >= INT_MIN)) (PreH20 : (index < minimumIndex)) (PreH21 : ((width * currentHeight ) <= maximumArea)) (PreH22 : (2 <= heightSize_pre)) (PreH23 : (heightSize_pre <= 100000)) (PreH24 : ((Zlength (l)) = heightSize_pre)) (PreH25 : (1 <= k)) (PreH26 : (k < heightSize_pre)) (PreH27 : (index = (Znth k sorted_i_2 0))) (PreH28 : (currentHeight = (Znth k sorted_h_2 0))) (PreH29 : (currentHeight = (Znth index l 0))) (PreH30 : (0 <= index)) (PreH31 : (index < heightSize_pre)) (PreH32 : (0 <= minimumIndex)) (PreH33 : (minimumIndex <= maximumIndex)) (PreH34 : (maximumIndex < heightSize_pre)) (PreH35 : (0 <= currentHeight)) (PreH36 : (currentHeight <= 10000)) (PreH37 : (0 <= distanceToMinimum)) (PreH38 : (distanceToMinimum <= 99999)) (PreH39 : (0 <= distanceToMaximum)) (PreH40 : (distanceToMaximum <= 99999)) (PreH41 : (distanceToMinimum = (minimumIndex - index ))) (PreH42 : (distanceToMaximum = (maximumIndex - index ))) (PreH43 : (distanceToMinimum <= width)) (PreH44 : (distanceToMaximum <= width)) (PreH45 : (width = distanceToMaximum)) (PreH46 : (0 <= width)) (PreH47 : (width <= 99999)) (PreH48 : (0 <= maximumArea)) (PreH49 : (maximumArea <= 999990000)) (PreH50 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH51 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH52 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH53 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) index maximumIndex )
.

Definition maxAreaNLogN_entail_wit_9_9 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (width * currentHeight )) ” 
  &&  “ ((width * currentHeight ) <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) (width * currentHeight ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMinimum * currentHeight ) ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_9_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_9_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMinimum * currentHeight ) )
.

Definition maxAreaNLogN_entail_wit_9_9_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex )
.

Definition maxAreaNLogN_entail_wit_9_10 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (width * currentHeight )) ” 
  &&  “ ((width * currentHeight ) <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) (width * currentHeight ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMaximum * currentHeight ) ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_10_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_10_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMaximum * currentHeight ) )
.

Definition maxAreaNLogN_entail_wit_9_10_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex )
.

Definition maxAreaNLogN_entail_wit_9_11 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (width * currentHeight )) ” 
  &&  “ ((width * currentHeight ) <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) (width * currentHeight ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMinimum * currentHeight ) ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_11_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_11_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMinimum * currentHeight ) )
.

Definition maxAreaNLogN_entail_wit_9_11_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex )
.

Definition maxAreaNLogN_entail_wit_9_12 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (width * currentHeight )) ” 
  &&  “ ((width * currentHeight ) <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) (width * currentHeight ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMaximum * currentHeight ) ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_12_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_12_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMaximum * currentHeight ) )
.

Definition maxAreaNLogN_entail_wit_9_12_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex )
.

Definition maxAreaNLogN_entail_wit_9_13 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (width * currentHeight )) ” 
  &&  “ ((width * currentHeight ) <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) (width * currentHeight ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMinimum * currentHeight ) ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_13_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_13_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMinimum * currentHeight ) )
.

Definition maxAreaNLogN_entail_wit_9_13_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex )
.

Definition maxAreaNLogN_entail_wit_9_14 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (width * currentHeight )) ” 
  &&  “ ((width * currentHeight ) <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) (width * currentHeight ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMaximum * currentHeight ) ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_14_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_14_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMaximum * currentHeight ) )
.

Definition maxAreaNLogN_entail_wit_9_14_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex )
.

Definition maxAreaNLogN_entail_wit_9_15 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (width * currentHeight )) ” 
  &&  “ ((width * currentHeight ) <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) (width * currentHeight ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMinimum * currentHeight ) ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_15_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_15_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMinimum * currentHeight ) )
.

Definition maxAreaNLogN_entail_wit_9_15_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex )
.

Definition maxAreaNLogN_entail_wit_9_16 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= (width * currentHeight )) ” 
  &&  “ ((width * currentHeight ) <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) (width * currentHeight ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMaximum * currentHeight ) ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_16_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_16_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) (distanceToMaximum * currentHeight ) )
.

Definition maxAreaNLogN_entail_wit_9_16_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) > maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex )
.

Definition maxAreaNLogN_entail_wit_9_17 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_17_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_17_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea )
.

Definition maxAreaNLogN_entail_wit_9_17_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex )
.

Definition maxAreaNLogN_entail_wit_9_18 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_18_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_18_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea )
.

Definition maxAreaNLogN_entail_wit_9_18_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex )
.

Definition maxAreaNLogN_entail_wit_9_19 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_19_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_19_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea )
.

Definition maxAreaNLogN_entail_wit_9_19_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex )
.

Definition maxAreaNLogN_entail_wit_9_20 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_20_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_20_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea )
.

Definition maxAreaNLogN_entail_wit_9_20_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (index - minimumIndex ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex )
.

Definition maxAreaNLogN_entail_wit_9_21 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_21_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_21_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea )
.

Definition maxAreaNLogN_entail_wit_9_21_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex )
.

Definition maxAreaNLogN_entail_wit_9_22 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_22_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_22_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea )
.

Definition maxAreaNLogN_entail_wit_9_22_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (index - maximumIndex ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex )
.

Definition maxAreaNLogN_entail_wit_9_23 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_23_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_23_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea )
.

Definition maxAreaNLogN_entail_wit_9_23_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMinimum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex )
.

Definition maxAreaNLogN_entail_wit_9_24 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i (k + 1 ) minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i (k + 1 ) maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_9_24_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))
.

Definition maxAreaNLogN_entail_wit_9_24_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedContainerMaximumNLogN l sorted_i_2 (k + 1 ) maximumArea )
.

Definition maxAreaNLogN_entail_wit_9_24_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (k: Z) (index: Z) (currentHeight: Z) (minimumIndex: Z) (maximumIndex: Z) (distanceToMinimum: Z) (distanceToMaximum: Z) (width: Z) (maximumArea: Z) (PreH1 : (index <= maximumIndex)) (PreH2 : (index >= minimumIndex)) (PreH3 : ((width * currentHeight ) <= maximumArea)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (1 <= k)) (PreH8 : (k < heightSize_pre)) (PreH9 : (index = (Znth k sorted_i_2 0))) (PreH10 : (currentHeight = (Znth k sorted_h_2 0))) (PreH11 : (currentHeight = (Znth index l 0))) (PreH12 : (0 <= index)) (PreH13 : (index < heightSize_pre)) (PreH14 : (0 <= minimumIndex)) (PreH15 : (minimumIndex <= maximumIndex)) (PreH16 : (maximumIndex < heightSize_pre)) (PreH17 : (0 <= currentHeight)) (PreH18 : (currentHeight <= 10000)) (PreH19 : (0 <= distanceToMinimum)) (PreH20 : (distanceToMinimum <= 99999)) (PreH21 : (0 <= distanceToMaximum)) (PreH22 : (distanceToMaximum <= 99999)) (PreH23 : (distanceToMinimum = (minimumIndex - index ))) (PreH24 : (distanceToMaximum = (maximumIndex - index ))) (PreH25 : (distanceToMinimum <= width)) (PreH26 : (distanceToMaximum <= width)) (PreH27 : (width = distanceToMaximum)) (PreH28 : (0 <= width)) (PreH29 : (width <= 99999)) (PreH30 : (0 <= maximumArea)) (PreH31 : (maximumArea <= 999990000)) (PreH32 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH33 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH34 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH35 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < heightSize_pre)) -> ((0 <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= 10000)))) ,
  (ProcessedIndexEndpointsNLogN sorted_i_2 (k + 1 ) minimumIndex maximumIndex )
.

Definition maxAreaNLogN_entail_wit_10 := 
(
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i_2: (@list Z)) (buffer_h_2: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (k >= heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : (0 <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH15 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (MaximumContainerArea l maximumArea ) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex < heightSize_pre) ” 
  &&  “ (0 <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (k >= heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : (0 <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH15 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  TT && emp 
|--
  “ (MaximumContainerArea l maximumArea ) ”
  &&  emp
).

Definition maxAreaNLogN_entail_wit_10_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (k >= heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : (0 <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i_2 k minimumIndex maximumIndex )) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i_2 k maximumArea )) (PreH15 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  (MaximumContainerArea l maximumArea )
.

Definition maxAreaNLogN_return_wit_1 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h_2: (@list Z)) (sorted_i_2: (@list Z)) (buffer_h_2: (@list Z)) (buffer_i_2: (@list Z)) (maximumArea: Z) (minimumIndex: Z) (maximumIndex: Z) (PreH1 : (MaximumContainerArea l maximumArea )) (PreH2 : (0 <= maximumArea)) (PreH3 : (maximumArea <= 999990000)) (PreH4 : (0 <= minimumIndex)) (PreH5 : (minimumIndex < heightSize_pre)) (PreH6 : (0 <= maximumIndex)) (PreH7 : (maximumIndex < heightSize_pre)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (SortedHeightIndexWorkspaceNLogN l sorted_h_2 sorted_i_2 )) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h_2 )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i_2 )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h_2 )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i_2 )
|--
  EX (buffer_i: (@list Z))  (buffer_h: (@list Z))  (sorted_h: (@list Z))  (sorted_i: (@list Z)) ,
  “ (MaximumContainerArea l maximumArea ) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ”
  &&  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
.

Definition maxAreaNLogN_partial_solve_wit_1 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_i: (@list Z)) (work_h: (@list Z)) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h)) = k)) (PreH8 : ((Zlength (work_i)) = k)) (PreH9 : ((Zlength (buffer_h)) = k)) (PreH10 : ((Zlength (buffer_i)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h work_i k )) (PreH12 : (WorkspacePrefixNLogN l buffer_h buffer_i k )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre k work_h )
  **  (IntArray.undef_seg workHeight_pre k heightSize_pre )
  **  (IntArray.full workIndex_pre k work_i )
  **  (IntArray.undef_seg workIndex_pre k heightSize_pre )
  **  (IntArray.full bufferHeight_pre k buffer_h )
  **  (IntArray.undef_seg bufferHeight_pre k heightSize_pre )
  **  (IntArray.full bufferIndex_pre k buffer_i )
  **  (IntArray.undef_seg bufferIndex_pre k heightSize_pre )
|--
  “ (k < heightSize_pre) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= heightSize_pre) ” 
  &&  “ ((Zlength (work_h)) = k) ” 
  &&  “ ((Zlength (work_i)) = k) ” 
  &&  “ ((Zlength (buffer_h)) = k) ” 
  &&  “ ((Zlength (buffer_i)) = k) ” 
  &&  “ (WorkspacePrefixNLogN l work_h work_i k ) ” 
  &&  “ (WorkspacePrefixNLogN l buffer_h buffer_i k ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (((height_pre + (k * sizeof(INT)))) # Int  |-> (Znth k l 0))
  **  (IntArray.missing_i height_pre k 0 heightSize_pre l )
  **  (IntArray.full workHeight_pre k work_h )
  **  (IntArray.undef_seg workHeight_pre k heightSize_pre )
  **  (IntArray.full workIndex_pre k work_i )
  **  (IntArray.undef_seg workIndex_pre k heightSize_pre )
  **  (IntArray.full bufferHeight_pre k buffer_h )
  **  (IntArray.undef_seg bufferHeight_pre k heightSize_pre )
  **  (IntArray.full bufferIndex_pre k buffer_i )
  **  (IntArray.undef_seg bufferIndex_pre k heightSize_pre )
.

Definition maxAreaNLogN_partial_solve_wit_2 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_i: (@list Z)) (work_h: (@list Z)) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h)) = k)) (PreH8 : ((Zlength (work_i)) = k)) (PreH9 : ((Zlength (buffer_h)) = k)) (PreH10 : ((Zlength (buffer_i)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h work_i k )) (PreH12 : (WorkspacePrefixNLogN l buffer_h buffer_i k )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre k work_h )
  **  (IntArray.undef_seg workHeight_pre k heightSize_pre )
  **  (IntArray.full workIndex_pre k work_i )
  **  (IntArray.undef_seg workIndex_pre k heightSize_pre )
  **  (IntArray.full bufferHeight_pre k buffer_h )
  **  (IntArray.undef_seg bufferHeight_pre k heightSize_pre )
  **  (IntArray.full bufferIndex_pre k buffer_i )
  **  (IntArray.undef_seg bufferIndex_pre k heightSize_pre )
|--
  “ (k < heightSize_pre) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= heightSize_pre) ” 
  &&  “ ((Zlength (work_h)) = k) ” 
  &&  “ ((Zlength (work_i)) = k) ” 
  &&  “ ((Zlength (buffer_h)) = k) ” 
  &&  “ ((Zlength (buffer_i)) = k) ” 
  &&  “ (WorkspacePrefixNLogN l work_h work_i k ) ” 
  &&  “ (WorkspacePrefixNLogN l buffer_h buffer_i k ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (((workHeight_pre + (k * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg workHeight_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre k work_h )
  **  (IntArray.full workIndex_pre k work_i )
  **  (IntArray.undef_seg workIndex_pre k heightSize_pre )
  **  (IntArray.full bufferHeight_pre k buffer_h )
  **  (IntArray.undef_seg bufferHeight_pre k heightSize_pre )
  **  (IntArray.full bufferIndex_pre k buffer_i )
  **  (IntArray.undef_seg bufferIndex_pre k heightSize_pre )
.

Definition maxAreaNLogN_partial_solve_wit_3 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_i: (@list Z)) (work_h: (@list Z)) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h)) = k)) (PreH8 : ((Zlength (work_i)) = k)) (PreH9 : ((Zlength (buffer_h)) = k)) (PreH10 : ((Zlength (buffer_i)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h work_i k )) (PreH12 : (WorkspacePrefixNLogN l buffer_h buffer_i k )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  (IntArray.full workHeight_pre (k + 1 ) (app (work_h) ((cons ((Znth k l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg workHeight_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workIndex_pre k work_i )
  **  (IntArray.undef_seg workIndex_pre k heightSize_pre )
  **  (IntArray.full bufferHeight_pre k buffer_h )
  **  (IntArray.undef_seg bufferHeight_pre k heightSize_pre )
  **  (IntArray.full bufferIndex_pre k buffer_i )
  **  (IntArray.undef_seg bufferIndex_pre k heightSize_pre )
|--
  “ (k < heightSize_pre) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= heightSize_pre) ” 
  &&  “ ((Zlength (work_h)) = k) ” 
  &&  “ ((Zlength (work_i)) = k) ” 
  &&  “ ((Zlength (buffer_h)) = k) ” 
  &&  “ ((Zlength (buffer_i)) = k) ” 
  &&  “ (WorkspacePrefixNLogN l work_h work_i k ) ” 
  &&  “ (WorkspacePrefixNLogN l buffer_h buffer_i k ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (((workIndex_pre + (k * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg workIndex_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full workHeight_pre (k + 1 ) (app (work_h) ((cons ((Znth k l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg workHeight_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workIndex_pre k work_i )
  **  (IntArray.full bufferHeight_pre k buffer_h )
  **  (IntArray.undef_seg bufferHeight_pre k heightSize_pre )
  **  (IntArray.full bufferIndex_pre k buffer_i )
  **  (IntArray.undef_seg bufferIndex_pre k heightSize_pre )
.

Definition maxAreaNLogN_partial_solve_wit_4 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_i: (@list Z)) (work_h: (@list Z)) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h)) = k)) (PreH8 : ((Zlength (work_i)) = k)) (PreH9 : ((Zlength (buffer_h)) = k)) (PreH10 : ((Zlength (buffer_i)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h work_i k )) (PreH12 : (WorkspacePrefixNLogN l buffer_h buffer_i k )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  (IntArray.full workIndex_pre (k + 1 ) (app (work_i) ((cons (k) ((@nil Z))))) )
  **  (IntArray.undef_seg workIndex_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full workHeight_pre (k + 1 ) (app (work_h) ((cons ((Znth k l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg workHeight_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre k buffer_h )
  **  (IntArray.undef_seg bufferHeight_pre k heightSize_pre )
  **  (IntArray.full bufferIndex_pre k buffer_i )
  **  (IntArray.undef_seg bufferIndex_pre k heightSize_pre )
|--
  “ (k < heightSize_pre) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= heightSize_pre) ” 
  &&  “ ((Zlength (work_h)) = k) ” 
  &&  “ ((Zlength (work_i)) = k) ” 
  &&  “ ((Zlength (buffer_h)) = k) ” 
  &&  “ ((Zlength (buffer_i)) = k) ” 
  &&  “ (WorkspacePrefixNLogN l work_h work_i k ) ” 
  &&  “ (WorkspacePrefixNLogN l buffer_h buffer_i k ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (((bufferHeight_pre + (k * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg bufferHeight_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full workIndex_pre (k + 1 ) (app (work_i) ((cons (k) ((@nil Z))))) )
  **  (IntArray.undef_seg workIndex_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full workHeight_pre (k + 1 ) (app (work_h) ((cons ((Znth k l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg workHeight_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre k buffer_h )
  **  (IntArray.full bufferIndex_pre k buffer_i )
  **  (IntArray.undef_seg bufferIndex_pre k heightSize_pre )
.

Definition maxAreaNLogN_partial_solve_wit_5 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (work_i: (@list Z)) (work_h: (@list Z)) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : ((Zlength (work_h)) = k)) (PreH8 : ((Zlength (work_i)) = k)) (PreH9 : ((Zlength (buffer_h)) = k)) (PreH10 : ((Zlength (buffer_i)) = k)) (PreH11 : (WorkspacePrefixNLogN l work_h work_i k )) (PreH12 : (WorkspacePrefixNLogN l buffer_h buffer_i k )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  (IntArray.full bufferHeight_pre (k + 1 ) (app (buffer_h) ((cons ((Znth k l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg bufferHeight_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full workIndex_pre (k + 1 ) (app (work_i) ((cons (k) ((@nil Z))))) )
  **  (IntArray.undef_seg workIndex_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full workHeight_pre (k + 1 ) (app (work_h) ((cons ((Znth k l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg workHeight_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferIndex_pre k buffer_i )
  **  (IntArray.undef_seg bufferIndex_pre k heightSize_pre )
|--
  “ (k < heightSize_pre) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= heightSize_pre) ” 
  &&  “ ((Zlength (work_h)) = k) ” 
  &&  “ ((Zlength (work_i)) = k) ” 
  &&  “ ((Zlength (buffer_h)) = k) ” 
  &&  “ ((Zlength (buffer_i)) = k) ” 
  &&  “ (WorkspacePrefixNLogN l work_h work_i k ) ” 
  &&  “ (WorkspacePrefixNLogN l buffer_h buffer_i k ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (((bufferIndex_pre + (k * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg bufferIndex_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full bufferHeight_pre (k + 1 ) (app (buffer_h) ((cons ((Znth k l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg bufferHeight_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full workIndex_pre (k + 1 ) (app (work_i) ((cons (k) ((@nil Z))))) )
  **  (IntArray.undef_seg workIndex_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full workHeight_pre (k + 1 ) (app (work_h) ((cons ((Znth k l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg workHeight_pre (k + 1 ) heightSize_pre )
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferIndex_pre k buffer_i )
.

Definition maxAreaNLogN_partial_solve_wit_6_pure := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (work0_h: (@list Z)) (work0_i: (@list Z)) (buffer0_h: (@list Z)) (buffer0_i: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : ((Zlength (work0_h)) = heightSize_pre)) (PreH5 : ((Zlength (work0_i)) = heightSize_pre)) (PreH6 : ((Zlength (buffer0_h)) = heightSize_pre)) (PreH7 : ((Zlength (buffer0_i)) = heightSize_pre)) (PreH8 : (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre )) (PreH9 : (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre )) (PreH10 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "workHeight" ) )) # Ptr  |-> workHeight_pre)
  **  ((( &( "workIndex" ) )) # Ptr  |-> workIndex_pre)
  **  ((( &( "bufferHeight" ) )) # Ptr  |-> bufferHeight_pre)
  **  ((( &( "bufferIndex" ) )) # Ptr  |-> bufferIndex_pre)
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre work0_h )
  **  (IntArray.full workIndex_pre heightSize_pre work0_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer0_i )
|--
  “ ((Zlength (work0_h)) = heightSize_pre) ” 
  &&  “ ((Zlength (work0_i)) = heightSize_pre) ” 
  &&  “ ((Zlength (buffer0_h)) = heightSize_pre) ” 
  &&  “ ((Zlength (buffer0_i)) = heightSize_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ”
.

Definition maxAreaNLogN_partial_solve_wit_6_aux := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (work0_h: (@list Z)) (work0_i: (@list Z)) (buffer0_h: (@list Z)) (buffer0_i: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : ((Zlength (work0_h)) = heightSize_pre)) (PreH5 : ((Zlength (work0_i)) = heightSize_pre)) (PreH6 : ((Zlength (buffer0_h)) = heightSize_pre)) (PreH7 : ((Zlength (buffer0_i)) = heightSize_pre)) (PreH8 : (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre )) (PreH9 : (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre )) (PreH10 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre work0_h )
  **  (IntArray.full workIndex_pre heightSize_pre work0_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer0_i )
|--
  “ ((Zlength (work0_h)) = heightSize_pre) ” 
  &&  “ ((Zlength (work0_i)) = heightSize_pre) ” 
  &&  “ ((Zlength (buffer0_h)) = heightSize_pre) ” 
  &&  “ ((Zlength (buffer0_i)) = heightSize_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ ((Zlength (work0_h)) = heightSize_pre) ” 
  &&  “ ((Zlength (work0_i)) = heightSize_pre) ” 
  &&  “ ((Zlength (buffer0_h)) = heightSize_pre) ” 
  &&  “ ((Zlength (buffer0_i)) = heightSize_pre) ” 
  &&  “ (WorkspacePrefixNLogN l work0_h work0_i heightSize_pre ) ” 
  &&  “ (WorkspacePrefixNLogN l buffer0_h buffer0_i heightSize_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (IntArray.full workHeight_pre heightSize_pre work0_h )
  **  (IntArray.full workIndex_pre heightSize_pre work0_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer0_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer0_i )
  **  (IntArray.full height_pre heightSize_pre l )
.

Definition maxAreaNLogN_partial_solve_wit_6 := maxAreaNLogN_partial_solve_wit_6_pure -> maxAreaNLogN_partial_solve_wit_6_aux.

Definition maxAreaNLogN_partial_solve_wit_7 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH5 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (((workIndex_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 sorted_i 0))
  **  (IntArray.missing_i workIndex_pre 0 0 heightSize_pre sorted_i )
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
.

Definition maxAreaNLogN_partial_solve_wit_8 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (buffer_h: (@list Z)) (buffer_i: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH5 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (((workIndex_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 sorted_i 0))
  **  (IntArray.missing_i workIndex_pre 0 0 heightSize_pre sorted_i )
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
.

Definition maxAreaNLogN_partial_solve_wit_9 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : (0 <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH15 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ (k < heightSize_pre) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (((workIndex_pre + (k * sizeof(INT)))) # Int  |-> (Znth k sorted_i 0))
  **  (IntArray.missing_i workIndex_pre k 0 heightSize_pre sorted_i )
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
.

Definition maxAreaNLogN_partial_solve_wit_10 := 
forall (bufferIndex_pre: Z) (bufferHeight_pre: Z) (workIndex_pre: Z) (workHeight_pre: Z) (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (buffer_i: (@list Z)) (buffer_h: (@list Z)) (sorted_h: (@list Z)) (sorted_i: (@list Z)) (maximumArea: Z) (maximumIndex: Z) (minimumIndex: Z) (k: Z) (PreH1 : (k < heightSize_pre)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (1 <= k)) (PreH6 : (k <= heightSize_pre)) (PreH7 : (0 <= minimumIndex)) (PreH8 : (minimumIndex <= maximumIndex)) (PreH9 : (maximumIndex < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i )) (PreH13 : (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex )) (PreH14 : (ProcessedContainerMaximumNLogN l sorted_i k maximumArea )) (PreH15 : forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000)))) ,
  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full workHeight_pre heightSize_pre sorted_h )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
|--
  “ (k < heightSize_pre) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k <= heightSize_pre) ” 
  &&  “ (0 <= minimumIndex) ” 
  &&  “ (minimumIndex <= maximumIndex) ” 
  &&  “ (maximumIndex < heightSize_pre) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (SortedHeightIndexWorkspaceNLogN l sorted_h sorted_i ) ” 
  &&  “ (ProcessedIndexEndpointsNLogN sorted_i k minimumIndex maximumIndex ) ” 
  &&  “ (ProcessedContainerMaximumNLogN l sorted_i k maximumArea ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < heightSize_pre)) -> ((0 <= (Znth p l 0)) /\ ((Znth p l 0) <= 10000))) ”
  &&  (((workHeight_pre + (k * sizeof(INT)))) # Int  |-> (Znth k sorted_h 0))
  **  (IntArray.missing_i workHeight_pre k 0 heightSize_pre sorted_h )
  **  (IntArray.full workIndex_pre heightSize_pre sorted_i )
  **  (IntArray.full height_pre heightSize_pre l )
  **  (IntArray.full bufferHeight_pre heightSize_pre buffer_h )
  **  (IntArray.full bufferIndex_pre heightSize_pre buffer_i )
.

Module Type VC_Correct.


Axiom proof_of_mergeHeightIndexRunsNLogN_safety_wit_1 : mergeHeightIndexRunsNLogN_safety_wit_1.
Axiom proof_of_mergeHeightIndexRunsNLogN_safety_wit_2 : mergeHeightIndexRunsNLogN_safety_wit_2.
Axiom proof_of_mergeHeightIndexRunsNLogN_safety_wit_3 : mergeHeightIndexRunsNLogN_safety_wit_3.
Axiom proof_of_mergeHeightIndexRunsNLogN_safety_wit_4 : mergeHeightIndexRunsNLogN_safety_wit_4.
Axiom proof_of_mergeHeightIndexRunsNLogN_safety_wit_5 : mergeHeightIndexRunsNLogN_safety_wit_5.
Axiom proof_of_mergeHeightIndexRunsNLogN_safety_wit_6 : mergeHeightIndexRunsNLogN_safety_wit_6.
Axiom proof_of_mergeHeightIndexRunsNLogN_safety_wit_7 : mergeHeightIndexRunsNLogN_safety_wit_7.
Axiom proof_of_mergeHeightIndexRunsNLogN_safety_wit_8 : mergeHeightIndexRunsNLogN_safety_wit_8.
Axiom proof_of_mergeHeightIndexRunsNLogN_safety_wit_9 : mergeHeightIndexRunsNLogN_safety_wit_9.
Axiom proof_of_mergeHeightIndexRunsNLogN_entail_wit_1 : mergeHeightIndexRunsNLogN_entail_wit_1.
Axiom proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_1 : mergeHeightIndexRunsNLogN_entail_wit_2_1.
Axiom proof_of_mergeHeightIndexRunsNLogN_entail_wit_2_2 : mergeHeightIndexRunsNLogN_entail_wit_2_2.
Axiom proof_of_mergeHeightIndexRunsNLogN_entail_wit_3_1 : mergeHeightIndexRunsNLogN_entail_wit_3_1.
Axiom proof_of_mergeHeightIndexRunsNLogN_entail_wit_3_2 : mergeHeightIndexRunsNLogN_entail_wit_3_2.
Axiom proof_of_mergeHeightIndexRunsNLogN_entail_wit_4 : mergeHeightIndexRunsNLogN_entail_wit_4.
Axiom proof_of_mergeHeightIndexRunsNLogN_entail_wit_5_1 : mergeHeightIndexRunsNLogN_entail_wit_5_1.
Axiom proof_of_mergeHeightIndexRunsNLogN_entail_wit_5_2 : mergeHeightIndexRunsNLogN_entail_wit_5_2.
Axiom proof_of_mergeHeightIndexRunsNLogN_entail_wit_6 : mergeHeightIndexRunsNLogN_entail_wit_6.
Axiom proof_of_mergeHeightIndexRunsNLogN_return_wit_1 : mergeHeightIndexRunsNLogN_return_wit_1.
Axiom proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_1 : mergeHeightIndexRunsNLogN_partial_solve_wit_1.
Axiom proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_2 : mergeHeightIndexRunsNLogN_partial_solve_wit_2.
Axiom proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_3 : mergeHeightIndexRunsNLogN_partial_solve_wit_3.
Axiom proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_4 : mergeHeightIndexRunsNLogN_partial_solve_wit_4.
Axiom proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_5 : mergeHeightIndexRunsNLogN_partial_solve_wit_5.
Axiom proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_6 : mergeHeightIndexRunsNLogN_partial_solve_wit_6.
Axiom proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_7 : mergeHeightIndexRunsNLogN_partial_solve_wit_7.
Axiom proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_8 : mergeHeightIndexRunsNLogN_partial_solve_wit_8.
Axiom proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_9 : mergeHeightIndexRunsNLogN_partial_solve_wit_9.
Axiom proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_10 : mergeHeightIndexRunsNLogN_partial_solve_wit_10.
Axiom proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_11 : mergeHeightIndexRunsNLogN_partial_solve_wit_11.
Axiom proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_12 : mergeHeightIndexRunsNLogN_partial_solve_wit_12.
Axiom proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_13 : mergeHeightIndexRunsNLogN_partial_solve_wit_13.
Axiom proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_14 : mergeHeightIndexRunsNLogN_partial_solve_wit_14.
Axiom proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_15 : mergeHeightIndexRunsNLogN_partial_solve_wit_15.
Axiom proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_16 : mergeHeightIndexRunsNLogN_partial_solve_wit_16.
Axiom proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_17 : mergeHeightIndexRunsNLogN_partial_solve_wit_17.
Axiom proof_of_mergeHeightIndexRunsNLogN_partial_solve_wit_18 : mergeHeightIndexRunsNLogN_partial_solve_wit_18.
Axiom proof_of_sortHeightIndexRangeNLogN_safety_wit_1 : sortHeightIndexRangeNLogN_safety_wit_1.
Axiom proof_of_sortHeightIndexRangeNLogN_safety_wit_2 : sortHeightIndexRangeNLogN_safety_wit_2.
Axiom proof_of_sortHeightIndexRangeNLogN_safety_wit_3 : sortHeightIndexRangeNLogN_safety_wit_3.
Axiom proof_of_sortHeightIndexRangeNLogN_safety_wit_4 : sortHeightIndexRangeNLogN_safety_wit_4.
Axiom proof_of_sortHeightIndexRangeNLogN_safety_wit_5 : sortHeightIndexRangeNLogN_safety_wit_5.
Axiom proof_of_sortHeightIndexRangeNLogN_safety_wit_6 : sortHeightIndexRangeNLogN_safety_wit_6.
Axiom proof_of_sortHeightIndexRangeNLogN_safety_wit_7 : sortHeightIndexRangeNLogN_safety_wit_7.
Axiom proof_of_sortHeightIndexRangeNLogN_entail_wit_1 : sortHeightIndexRangeNLogN_entail_wit_1.
Axiom proof_of_sortHeightIndexRangeNLogN_entail_wit_2 : sortHeightIndexRangeNLogN_entail_wit_2.
Axiom proof_of_sortHeightIndexRangeNLogN_entail_wit_3 : sortHeightIndexRangeNLogN_entail_wit_3.
Axiom proof_of_sortHeightIndexRangeNLogN_entail_wit_4 : sortHeightIndexRangeNLogN_entail_wit_4.
Axiom proof_of_sortHeightIndexRangeNLogN_return_wit_1 : sortHeightIndexRangeNLogN_return_wit_1.
Axiom proof_of_sortHeightIndexRangeNLogN_return_wit_2 : sortHeightIndexRangeNLogN_return_wit_2.
Axiom proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_1_pure : sortHeightIndexRangeNLogN_partial_solve_wit_1_pure.
Axiom proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_1 : sortHeightIndexRangeNLogN_partial_solve_wit_1.
Axiom proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2_pure : sortHeightIndexRangeNLogN_partial_solve_wit_2_pure.
Axiom proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_2 : sortHeightIndexRangeNLogN_partial_solve_wit_2.
Axiom proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_3_pure : sortHeightIndexRangeNLogN_partial_solve_wit_3_pure.
Axiom proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_3 : sortHeightIndexRangeNLogN_partial_solve_wit_3.
Axiom proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_4 : sortHeightIndexRangeNLogN_partial_solve_wit_4.
Axiom proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_5 : sortHeightIndexRangeNLogN_partial_solve_wit_5.
Axiom proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_6 : sortHeightIndexRangeNLogN_partial_solve_wit_6.
Axiom proof_of_sortHeightIndexRangeNLogN_partial_solve_wit_7 : sortHeightIndexRangeNLogN_partial_solve_wit_7.
Axiom proof_of_maxAreaNLogN_safety_wit_1 : maxAreaNLogN_safety_wit_1.
Axiom proof_of_maxAreaNLogN_safety_wit_2 : maxAreaNLogN_safety_wit_2.
Axiom proof_of_maxAreaNLogN_safety_wit_3 : maxAreaNLogN_safety_wit_3.
Axiom proof_of_maxAreaNLogN_safety_wit_4 : maxAreaNLogN_safety_wit_4.
Axiom proof_of_maxAreaNLogN_safety_wit_5 : maxAreaNLogN_safety_wit_5.
Axiom proof_of_maxAreaNLogN_safety_wit_6 : maxAreaNLogN_safety_wit_6.
Axiom proof_of_maxAreaNLogN_safety_wit_7 : maxAreaNLogN_safety_wit_7.
Axiom proof_of_maxAreaNLogN_safety_wit_8 : maxAreaNLogN_safety_wit_8.
Axiom proof_of_maxAreaNLogN_safety_wit_9 : maxAreaNLogN_safety_wit_9.
Axiom proof_of_maxAreaNLogN_safety_wit_10 : maxAreaNLogN_safety_wit_10.
Axiom proof_of_maxAreaNLogN_safety_wit_11 : maxAreaNLogN_safety_wit_11.
Axiom proof_of_maxAreaNLogN_safety_wit_12 : maxAreaNLogN_safety_wit_12.
Axiom proof_of_maxAreaNLogN_safety_wit_13 : maxAreaNLogN_safety_wit_13.
Axiom proof_of_maxAreaNLogN_safety_wit_14 : maxAreaNLogN_safety_wit_14.
Axiom proof_of_maxAreaNLogN_safety_wit_15 : maxAreaNLogN_safety_wit_15.
Axiom proof_of_maxAreaNLogN_safety_wit_16 : maxAreaNLogN_safety_wit_16.
Axiom proof_of_maxAreaNLogN_safety_wit_17 : maxAreaNLogN_safety_wit_17.
Axiom proof_of_maxAreaNLogN_safety_wit_18 : maxAreaNLogN_safety_wit_18.
Axiom proof_of_maxAreaNLogN_safety_wit_19 : maxAreaNLogN_safety_wit_19.
Axiom proof_of_maxAreaNLogN_safety_wit_20 : maxAreaNLogN_safety_wit_20.
Axiom proof_of_maxAreaNLogN_safety_wit_21 : maxAreaNLogN_safety_wit_21.
Axiom proof_of_maxAreaNLogN_safety_wit_22 : maxAreaNLogN_safety_wit_22.
Axiom proof_of_maxAreaNLogN_safety_wit_23 : maxAreaNLogN_safety_wit_23.
Axiom proof_of_maxAreaNLogN_safety_wit_24 : maxAreaNLogN_safety_wit_24.
Axiom proof_of_maxAreaNLogN_safety_wit_25 : maxAreaNLogN_safety_wit_25.
Axiom proof_of_maxAreaNLogN_safety_wit_26 : maxAreaNLogN_safety_wit_26.
Axiom proof_of_maxAreaNLogN_safety_wit_27 : maxAreaNLogN_safety_wit_27.
Axiom proof_of_maxAreaNLogN_safety_wit_28 : maxAreaNLogN_safety_wit_28.
Axiom proof_of_maxAreaNLogN_safety_wit_29 : maxAreaNLogN_safety_wit_29.
Axiom proof_of_maxAreaNLogN_safety_wit_30 : maxAreaNLogN_safety_wit_30.
Axiom proof_of_maxAreaNLogN_safety_wit_31 : maxAreaNLogN_safety_wit_31.
Axiom proof_of_maxAreaNLogN_safety_wit_32 : maxAreaNLogN_safety_wit_32.
Axiom proof_of_maxAreaNLogN_safety_wit_33 : maxAreaNLogN_safety_wit_33.
Axiom proof_of_maxAreaNLogN_safety_wit_34 : maxAreaNLogN_safety_wit_34.
Axiom proof_of_maxAreaNLogN_safety_wit_35 : maxAreaNLogN_safety_wit_35.
Axiom proof_of_maxAreaNLogN_safety_wit_36 : maxAreaNLogN_safety_wit_36.
Axiom proof_of_maxAreaNLogN_safety_wit_37 : maxAreaNLogN_safety_wit_37.
Axiom proof_of_maxAreaNLogN_safety_wit_38 : maxAreaNLogN_safety_wit_38.
Axiom proof_of_maxAreaNLogN_safety_wit_39 : maxAreaNLogN_safety_wit_39.
Axiom proof_of_maxAreaNLogN_safety_wit_40 : maxAreaNLogN_safety_wit_40.
Axiom proof_of_maxAreaNLogN_safety_wit_41 : maxAreaNLogN_safety_wit_41.
Axiom proof_of_maxAreaNLogN_safety_wit_42 : maxAreaNLogN_safety_wit_42.
Axiom proof_of_maxAreaNLogN_safety_wit_43 : maxAreaNLogN_safety_wit_43.
Axiom proof_of_maxAreaNLogN_safety_wit_44 : maxAreaNLogN_safety_wit_44.
Axiom proof_of_maxAreaNLogN_safety_wit_45 : maxAreaNLogN_safety_wit_45.
Axiom proof_of_maxAreaNLogN_safety_wit_46 : maxAreaNLogN_safety_wit_46.
Axiom proof_of_maxAreaNLogN_safety_wit_47 : maxAreaNLogN_safety_wit_47.
Axiom proof_of_maxAreaNLogN_safety_wit_48 : maxAreaNLogN_safety_wit_48.
Axiom proof_of_maxAreaNLogN_safety_wit_49 : maxAreaNLogN_safety_wit_49.
Axiom proof_of_maxAreaNLogN_safety_wit_50 : maxAreaNLogN_safety_wit_50.
Axiom proof_of_maxAreaNLogN_safety_wit_51 : maxAreaNLogN_safety_wit_51.
Axiom proof_of_maxAreaNLogN_safety_wit_52 : maxAreaNLogN_safety_wit_52.
Axiom proof_of_maxAreaNLogN_safety_wit_53 : maxAreaNLogN_safety_wit_53.
Axiom proof_of_maxAreaNLogN_safety_wit_54 : maxAreaNLogN_safety_wit_54.
Axiom proof_of_maxAreaNLogN_safety_wit_55 : maxAreaNLogN_safety_wit_55.
Axiom proof_of_maxAreaNLogN_safety_wit_56 : maxAreaNLogN_safety_wit_56.
Axiom proof_of_maxAreaNLogN_safety_wit_57 : maxAreaNLogN_safety_wit_57.
Axiom proof_of_maxAreaNLogN_safety_wit_58 : maxAreaNLogN_safety_wit_58.
Axiom proof_of_maxAreaNLogN_safety_wit_59 : maxAreaNLogN_safety_wit_59.
Axiom proof_of_maxAreaNLogN_safety_wit_60 : maxAreaNLogN_safety_wit_60.
Axiom proof_of_maxAreaNLogN_safety_wit_61 : maxAreaNLogN_safety_wit_61.
Axiom proof_of_maxAreaNLogN_safety_wit_62 : maxAreaNLogN_safety_wit_62.
Axiom proof_of_maxAreaNLogN_safety_wit_63 : maxAreaNLogN_safety_wit_63.
Axiom proof_of_maxAreaNLogN_safety_wit_64 : maxAreaNLogN_safety_wit_64.
Axiom proof_of_maxAreaNLogN_safety_wit_65 : maxAreaNLogN_safety_wit_65.
Axiom proof_of_maxAreaNLogN_safety_wit_66 : maxAreaNLogN_safety_wit_66.
Axiom proof_of_maxAreaNLogN_safety_wit_67 : maxAreaNLogN_safety_wit_67.
Axiom proof_of_maxAreaNLogN_safety_wit_68 : maxAreaNLogN_safety_wit_68.
Axiom proof_of_maxAreaNLogN_safety_wit_69 : maxAreaNLogN_safety_wit_69.
Axiom proof_of_maxAreaNLogN_safety_wit_70 : maxAreaNLogN_safety_wit_70.
Axiom proof_of_maxAreaNLogN_safety_wit_71 : maxAreaNLogN_safety_wit_71.
Axiom proof_of_maxAreaNLogN_safety_wit_72 : maxAreaNLogN_safety_wit_72.
Axiom proof_of_maxAreaNLogN_safety_wit_73 : maxAreaNLogN_safety_wit_73.
Axiom proof_of_maxAreaNLogN_safety_wit_74 : maxAreaNLogN_safety_wit_74.
Axiom proof_of_maxAreaNLogN_safety_wit_75 : maxAreaNLogN_safety_wit_75.
Axiom proof_of_maxAreaNLogN_safety_wit_76 : maxAreaNLogN_safety_wit_76.
Axiom proof_of_maxAreaNLogN_entail_wit_1 : maxAreaNLogN_entail_wit_1.
Axiom proof_of_maxAreaNLogN_entail_wit_2 : maxAreaNLogN_entail_wit_2.
Axiom proof_of_maxAreaNLogN_entail_wit_3 : maxAreaNLogN_entail_wit_3.
Axiom proof_of_maxAreaNLogN_entail_wit_4 : maxAreaNLogN_entail_wit_4.
Axiom proof_of_maxAreaNLogN_entail_wit_5 : maxAreaNLogN_entail_wit_5.
Axiom proof_of_maxAreaNLogN_entail_wit_6_1 : maxAreaNLogN_entail_wit_6_1.
Axiom proof_of_maxAreaNLogN_entail_wit_6_2 : maxAreaNLogN_entail_wit_6_2.
Axiom proof_of_maxAreaNLogN_entail_wit_6_3 : maxAreaNLogN_entail_wit_6_3.
Axiom proof_of_maxAreaNLogN_entail_wit_6_4 : maxAreaNLogN_entail_wit_6_4.
Axiom proof_of_maxAreaNLogN_entail_wit_6_5 : maxAreaNLogN_entail_wit_6_5.
Axiom proof_of_maxAreaNLogN_entail_wit_7_1 : maxAreaNLogN_entail_wit_7_1.
Axiom proof_of_maxAreaNLogN_entail_wit_7_2 : maxAreaNLogN_entail_wit_7_2.
Axiom proof_of_maxAreaNLogN_entail_wit_7_3 : maxAreaNLogN_entail_wit_7_3.
Axiom proof_of_maxAreaNLogN_entail_wit_7_4 : maxAreaNLogN_entail_wit_7_4.
Axiom proof_of_maxAreaNLogN_entail_wit_8_1 : maxAreaNLogN_entail_wit_8_1.
Axiom proof_of_maxAreaNLogN_entail_wit_8_2 : maxAreaNLogN_entail_wit_8_2.
Axiom proof_of_maxAreaNLogN_entail_wit_8_3 : maxAreaNLogN_entail_wit_8_3.
Axiom proof_of_maxAreaNLogN_entail_wit_8_4 : maxAreaNLogN_entail_wit_8_4.
Axiom proof_of_maxAreaNLogN_entail_wit_9_1 : maxAreaNLogN_entail_wit_9_1.
Axiom proof_of_maxAreaNLogN_entail_wit_9_2 : maxAreaNLogN_entail_wit_9_2.
Axiom proof_of_maxAreaNLogN_entail_wit_9_3 : maxAreaNLogN_entail_wit_9_3.
Axiom proof_of_maxAreaNLogN_entail_wit_9_4 : maxAreaNLogN_entail_wit_9_4.
Axiom proof_of_maxAreaNLogN_entail_wit_9_5 : maxAreaNLogN_entail_wit_9_5.
Axiom proof_of_maxAreaNLogN_entail_wit_9_6 : maxAreaNLogN_entail_wit_9_6.
Axiom proof_of_maxAreaNLogN_entail_wit_9_7 : maxAreaNLogN_entail_wit_9_7.
Axiom proof_of_maxAreaNLogN_entail_wit_9_8 : maxAreaNLogN_entail_wit_9_8.
Axiom proof_of_maxAreaNLogN_entail_wit_9_9 : maxAreaNLogN_entail_wit_9_9.
Axiom proof_of_maxAreaNLogN_entail_wit_9_10 : maxAreaNLogN_entail_wit_9_10.
Axiom proof_of_maxAreaNLogN_entail_wit_9_11 : maxAreaNLogN_entail_wit_9_11.
Axiom proof_of_maxAreaNLogN_entail_wit_9_12 : maxAreaNLogN_entail_wit_9_12.
Axiom proof_of_maxAreaNLogN_entail_wit_9_13 : maxAreaNLogN_entail_wit_9_13.
Axiom proof_of_maxAreaNLogN_entail_wit_9_14 : maxAreaNLogN_entail_wit_9_14.
Axiom proof_of_maxAreaNLogN_entail_wit_9_15 : maxAreaNLogN_entail_wit_9_15.
Axiom proof_of_maxAreaNLogN_entail_wit_9_16 : maxAreaNLogN_entail_wit_9_16.
Axiom proof_of_maxAreaNLogN_entail_wit_9_17 : maxAreaNLogN_entail_wit_9_17.
Axiom proof_of_maxAreaNLogN_entail_wit_9_18 : maxAreaNLogN_entail_wit_9_18.
Axiom proof_of_maxAreaNLogN_entail_wit_9_19 : maxAreaNLogN_entail_wit_9_19.
Axiom proof_of_maxAreaNLogN_entail_wit_9_20 : maxAreaNLogN_entail_wit_9_20.
Axiom proof_of_maxAreaNLogN_entail_wit_9_21 : maxAreaNLogN_entail_wit_9_21.
Axiom proof_of_maxAreaNLogN_entail_wit_9_22 : maxAreaNLogN_entail_wit_9_22.
Axiom proof_of_maxAreaNLogN_entail_wit_9_23 : maxAreaNLogN_entail_wit_9_23.
Axiom proof_of_maxAreaNLogN_entail_wit_9_24 : maxAreaNLogN_entail_wit_9_24.
Axiom proof_of_maxAreaNLogN_entail_wit_10 : maxAreaNLogN_entail_wit_10.
Axiom proof_of_maxAreaNLogN_return_wit_1 : maxAreaNLogN_return_wit_1.
Axiom proof_of_maxAreaNLogN_partial_solve_wit_1 : maxAreaNLogN_partial_solve_wit_1.
Axiom proof_of_maxAreaNLogN_partial_solve_wit_2 : maxAreaNLogN_partial_solve_wit_2.
Axiom proof_of_maxAreaNLogN_partial_solve_wit_3 : maxAreaNLogN_partial_solve_wit_3.
Axiom proof_of_maxAreaNLogN_partial_solve_wit_4 : maxAreaNLogN_partial_solve_wit_4.
Axiom proof_of_maxAreaNLogN_partial_solve_wit_5 : maxAreaNLogN_partial_solve_wit_5.
Axiom proof_of_maxAreaNLogN_partial_solve_wit_6_pure : maxAreaNLogN_partial_solve_wit_6_pure.
Axiom proof_of_maxAreaNLogN_partial_solve_wit_6 : maxAreaNLogN_partial_solve_wit_6.
Axiom proof_of_maxAreaNLogN_partial_solve_wit_7 : maxAreaNLogN_partial_solve_wit_7.
Axiom proof_of_maxAreaNLogN_partial_solve_wit_8 : maxAreaNLogN_partial_solve_wit_8.
Axiom proof_of_maxAreaNLogN_partial_solve_wit_9 : maxAreaNLogN_partial_solve_wit_9.
Axiom proof_of_maxAreaNLogN_partial_solve_wit_10 : maxAreaNLogN_partial_solve_wit_10.

End VC_Correct.
