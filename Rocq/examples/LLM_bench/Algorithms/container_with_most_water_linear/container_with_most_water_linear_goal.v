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
Require Import SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_linear.container_with_most_water_linear_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function maxAreaLinear -----*)

Definition maxAreaLinear_safety_wit_1 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : (height_pre <> 0)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (Forall (Z.le (0)) l )) (PreH6 : (Forall (Z.ge (10000)) l )) ,
  ((( &( "maximumArea" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  (IntArray.full height_pre heightSize_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxAreaLinear_safety_wit_2 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (PreH1 : (height_pre = 0)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : (height_pre <> 0)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (Forall (Z.le (0)) l )) (PreH7 : (Forall (Z.ge (10000)) l )) ,
  ((( &( "maximumArea" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  (IntArray.full height_pre heightSize_pre l )
|--
  “ False ”
.

Definition maxAreaLinear_safety_wit_3 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (PreH1 : (height_pre <> 0)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : (height_pre <> 0)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (Forall (Z.le (0)) l )) (PreH7 : (Forall (Z.ge (10000)) l )) ,
  ((( &( "maximumArea" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  (IntArray.full height_pre heightSize_pre l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition maxAreaLinear_safety_wit_4 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (PreH1 : (heightSize_pre < 2)) (PreH2 : (height_pre <> 0)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : (height_pre <> 0)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (Forall (Z.le (0)) l )) (PreH8 : (Forall (Z.ge (10000)) l )) ,
  ((( &( "maximumArea" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  (IntArray.full height_pre heightSize_pre l )
|--
  “ False ”
.

Definition maxAreaLinear_safety_wit_5 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (PreH1 : (heightSize_pre >= 2)) (PreH2 : (height_pre <> 0)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : (height_pre <> 0)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (Forall (Z.le (0)) l )) (PreH8 : (Forall (Z.ge (10000)) l )) ,
  ((( &( "maximumArea" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  (IntArray.full height_pre heightSize_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxAreaLinear_safety_wit_6 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (PreH1 : (heightSize_pre >= 2)) (PreH2 : (height_pre <> 0)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : (height_pre <> 0)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (Forall (Z.le (0)) l )) (PreH8 : (Forall (Z.ge (10000)) l )) ,
  ((( &( "maximumArea" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  (IntArray.full height_pre heightSize_pre l )
|--
  “ ((heightSize_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (heightSize_pre - 1 )) ”
.

Definition maxAreaLinear_safety_wit_7 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (PreH1 : (heightSize_pre >= 2)) (PreH2 : (height_pre <> 0)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : (height_pre <> 0)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (Forall (Z.le (0)) l )) (PreH8 : (Forall (Z.ge (10000)) l )) ,
  ((( &( "maximumArea" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  (IntArray.full height_pre heightSize_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition maxAreaLinear_safety_wit_8 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (PreH1 : (heightSize_pre >= 2)) (PreH2 : (height_pre <> 0)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : (height_pre <> 0)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (Forall (Z.le (0)) l )) (PreH8 : (Forall (Z.ge (10000)) l )) ,
  ((( &( "maximumArea" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> (heightSize_pre - 1 ))
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  (IntArray.full height_pre heightSize_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxAreaLinear_safety_wit_9 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (left < right)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= left)) (PreH6 : (left <= right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (0 <= maximumArea)) (PreH9 : (maximumArea <= 999990000)) (PreH10 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH11 : (Forall (Z.le (0)) l )) (PreH12 : (Forall (Z.ge (10000)) l )) ,
  ((( &( "width" ) )) # Int  |->_)
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
  **  (IntArray.full height_pre heightSize_pre l )
|--
  “ ((right - left ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (right - left )) ”
.

Definition maxAreaLinear_safety_wit_10 := 
(
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : ((Znth left l 0) < (Znth right l 0))) (PreH2 : (left < right)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= right)) (PreH8 : (right < heightSize_pre)) (PreH9 : (0 <= maximumArea)) (PreH10 : (maximumArea <= 999990000)) (PreH11 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH12 : (Forall (Z.le (0)) l )) (PreH13 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
  **  ((( &( "area" ) )) # Int  |->_)
  **  ((( &( "shorterHeight" ) )) # Int  |-> (Znth left l 0))
  **  ((( &( "width" ) )) # Int  |-> (right - left ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
|--
  “ (((right - left ) * (Znth left l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((right - left ) * (Znth left l 0) )) ”
) \/
(
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : ((Znth left l 0) < (Znth right l 0))) (PreH2 : (left < right)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= right)) (PreH8 : (right < heightSize_pre)) (PreH9 : (0 <= maximumArea)) (PreH10 : (maximumArea <= 999990000)) (PreH11 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH12 : (Forall (Z.le (0)) l )) (PreH13 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
  **  ((( &( "area" ) )) # Int  |->_)
  **  ((( &( "shorterHeight" ) )) # Int  |-> (Znth left l 0))
  **  ((( &( "width" ) )) # Int  |-> (right - left ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
|--
  “ (((right - left ) * (Znth left l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((right - left ) * (Znth left l 0) )) ”
).

Definition maxAreaLinear_safety_wit_10_split_goal_1 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : ((Znth left l 0) < (Znth right l 0))) (PreH2 : (left < right)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= right)) (PreH8 : (right < heightSize_pre)) (PreH9 : (0 <= maximumArea)) (PreH10 : (maximumArea <= 999990000)) (PreH11 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH12 : (Forall (Z.le (0)) l )) (PreH13 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
  **  ((( &( "area" ) )) # Int  |->_)
  **  ((( &( "shorterHeight" ) )) # Int  |-> (Znth left l 0))
  **  ((( &( "width" ) )) # Int  |-> (right - left ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
|--
  “ (((right - left ) * (Znth left l 0) ) <= INT_MAX) ”
.

Definition maxAreaLinear_safety_wit_10_split_goal_2 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : ((Znth left l 0) < (Znth right l 0))) (PreH2 : (left < right)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= right)) (PreH8 : (right < heightSize_pre)) (PreH9 : (0 <= maximumArea)) (PreH10 : (maximumArea <= 999990000)) (PreH11 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH12 : (Forall (Z.le (0)) l )) (PreH13 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
  **  ((( &( "area" ) )) # Int  |->_)
  **  ((( &( "shorterHeight" ) )) # Int  |-> (Znth left l 0))
  **  ((( &( "width" ) )) # Int  |-> (right - left ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
|--
  “ ((INT_MIN) <= ((right - left ) * (Znth left l 0) )) ”
.

Definition maxAreaLinear_safety_wit_11 := 
(
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : ((Znth left l 0) >= (Znth right l 0))) (PreH2 : (left < right)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= right)) (PreH8 : (right < heightSize_pre)) (PreH9 : (0 <= maximumArea)) (PreH10 : (maximumArea <= 999990000)) (PreH11 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH12 : (Forall (Z.le (0)) l )) (PreH13 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
  **  ((( &( "area" ) )) # Int  |->_)
  **  ((( &( "shorterHeight" ) )) # Int  |-> (Znth right l 0))
  **  ((( &( "width" ) )) # Int  |-> (right - left ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
|--
  “ (((right - left ) * (Znth right l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((right - left ) * (Znth right l 0) )) ”
) \/
(
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : ((Znth left l 0) >= (Znth right l 0))) (PreH2 : (left < right)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= right)) (PreH8 : (right < heightSize_pre)) (PreH9 : (0 <= maximumArea)) (PreH10 : (maximumArea <= 999990000)) (PreH11 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH12 : (Forall (Z.le (0)) l )) (PreH13 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
  **  ((( &( "area" ) )) # Int  |->_)
  **  ((( &( "shorterHeight" ) )) # Int  |-> (Znth right l 0))
  **  ((( &( "width" ) )) # Int  |-> (right - left ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
|--
  “ (((right - left ) * (Znth right l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((right - left ) * (Znth right l 0) )) ”
).

Definition maxAreaLinear_safety_wit_11_split_goal_1 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : ((Znth left l 0) >= (Znth right l 0))) (PreH2 : (left < right)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= right)) (PreH8 : (right < heightSize_pre)) (PreH9 : (0 <= maximumArea)) (PreH10 : (maximumArea <= 999990000)) (PreH11 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH12 : (Forall (Z.le (0)) l )) (PreH13 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
  **  ((( &( "area" ) )) # Int  |->_)
  **  ((( &( "shorterHeight" ) )) # Int  |-> (Znth right l 0))
  **  ((( &( "width" ) )) # Int  |-> (right - left ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
|--
  “ (((right - left ) * (Znth right l 0) ) <= INT_MAX) ”
.

Definition maxAreaLinear_safety_wit_11_split_goal_2 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : ((Znth left l 0) >= (Znth right l 0))) (PreH2 : (left < right)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= right)) (PreH8 : (right < heightSize_pre)) (PreH9 : (0 <= maximumArea)) (PreH10 : (maximumArea <= 999990000)) (PreH11 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH12 : (Forall (Z.le (0)) l )) (PreH13 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
  **  ((( &( "area" ) )) # Int  |->_)
  **  ((( &( "shorterHeight" ) )) # Int  |-> (Znth right l 0))
  **  ((( &( "width" ) )) # Int  |-> (right - left ))
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
|--
  “ ((INT_MIN) <= ((right - left ) * (Znth right l 0) )) ”
.

Definition maxAreaLinear_safety_wit_12 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (left: Z) (right: Z) (width: Z) (shorterHeight: Z) (area: Z) (maximumArea: Z) (PreH1 : ((Znth left l 0) < (Znth right l 0))) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= left)) (PreH6 : (left < right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (width = (right - left ))) (PreH9 : (1 <= width)) (PreH10 : (width <= 99999)) (PreH11 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH12 : (0 <= shorterHeight)) (PreH13 : (shorterHeight <= 10000)) (PreH14 : (area = (LinearContainerArea (l) (left) (right)))) (PreH15 : (0 <= area)) (PreH16 : (area <= maximumArea)) (PreH17 : (0 <= maximumArea)) (PreH18 : (maximumArea <= 999990000)) (PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH20 : (Forall (Z.le (0)) l )) (PreH21 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "shorterHeight" ) )) # Int  |-> shorterHeight)
  **  ((( &( "area" ) )) # Int  |-> area)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
|--
  “ ((left + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + 1 )) ”
.

Definition maxAreaLinear_safety_wit_13 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (left: Z) (right: Z) (width: Z) (shorterHeight: Z) (area: Z) (maximumArea: Z) (PreH1 : ((Znth left l 0) >= (Znth right l 0))) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= left)) (PreH6 : (left < right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (width = (right - left ))) (PreH9 : (1 <= width)) (PreH10 : (width <= 99999)) (PreH11 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH12 : (0 <= shorterHeight)) (PreH13 : (shorterHeight <= 10000)) (PreH14 : (area = (LinearContainerArea (l) (left) (right)))) (PreH15 : (0 <= area)) (PreH16 : (area <= maximumArea)) (PreH17 : (0 <= maximumArea)) (PreH18 : (maximumArea <= 999990000)) (PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH20 : (Forall (Z.le (0)) l )) (PreH21 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
  **  ((( &( "height" ) )) # Ptr  |-> height_pre)
  **  ((( &( "heightSize" ) )) # Int  |-> heightSize_pre)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "shorterHeight" ) )) # Int  |-> shorterHeight)
  **  ((( &( "area" ) )) # Int  |-> area)
  **  ((( &( "maximumArea" ) )) # Int  |-> maximumArea)
|--
  “ ((right - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (right - 1 )) ”
.

Definition maxAreaLinear_entail_wit_1 := 
(
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (PreH1 : (heightSize_pre >= 2)) (PreH2 : (height_pre <> 0)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : (height_pre <> 0)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (Forall (Z.le (0)) l )) (PreH8 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
|--
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (heightSize_pre - 1 )) ” 
  &&  “ ((heightSize_pre - 1 ) < heightSize_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 999990000) ” 
  &&  “ (LinearContainerTwoPointerInvariant l 0 (heightSize_pre - 1 ) 0 ) ” 
  &&  “ (Forall (Z.le (0)) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (IntArray.full height_pre heightSize_pre l )
) \/
(
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (PreH1 : (heightSize_pre >= 2)) (PreH2 : (height_pre <> 0)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : (height_pre <> 0)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (Forall (Z.le (0)) l )) (PreH8 : (Forall (Z.ge (10000)) l )) ,
  TT && emp 
|--
  “ (LinearContainerTwoPointerInvariant l 0 (heightSize_pre - 1 ) 0 ) ”
  &&  emp
).

Definition maxAreaLinear_entail_wit_1_split_goal_1 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (PreH1 : (heightSize_pre >= 2)) (PreH2 : (height_pre <> 0)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : (height_pre <> 0)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (Forall (Z.le (0)) l )) (PreH8 : (Forall (Z.ge (10000)) l )) ,
  (LinearContainerTwoPointerInvariant l 0 (heightSize_pre - 1 ) 0 )
.

Definition maxAreaLinear_entail_wit_2_1 := 
(
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth left l 0) ) > maximumArea)) (PreH2 : ((Znth left l 0) < (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
|--
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < right) ” 
  &&  “ (right < heightSize_pre) ” 
  &&  “ ((right - left ) = (right - left )) ” 
  &&  “ (1 <= (right - left )) ” 
  &&  “ ((right - left ) <= 99999) ” 
  &&  “ ((Znth left l 0) = (LinearContainerHeight (l) (left) (right))) ” 
  &&  “ (0 <= (Znth left l 0)) ” 
  &&  “ ((Znth left l 0) <= 10000) ” 
  &&  “ (((right - left ) * (Znth left l 0) ) = (LinearContainerArea (l) (left) (right))) ” 
  &&  “ (0 <= ((right - left ) * (Znth left l 0) )) ” 
  &&  “ (((right - left ) * (Znth left l 0) ) <= ((right - left ) * (Znth left l 0) )) ” 
  &&  “ (0 <= ((right - left ) * (Znth left l 0) )) ” 
  &&  “ (((right - left ) * (Znth left l 0) ) <= 999990000) ” 
  &&  “ (LinearContainerTwoPointerInvariant l left right ((right - left ) * (Znth left l 0) ) ) ” 
  &&  “ (Forall (Z.le (0)) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (IntArray.full height_pre heightSize_pre l )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth left l 0) ) > maximumArea)) (PreH2 : ((Znth left l 0) < (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  TT && emp 
|--
  “ (LinearContainerTwoPointerInvariant l left right ((right - left ) * (Znth left l 0) ) ) ” 
  &&  “ (((right - left ) * (Znth left l 0) ) <= 999990000) ” 
  &&  “ (((right - left ) * (Znth left l 0) ) = (LinearContainerArea (l) (left) (right))) ” 
  &&  “ ((Znth left l 0) <= 10000) ” 
  &&  “ (0 <= (Znth left l 0)) ” 
  &&  “ ((Znth left l 0) = (LinearContainerHeight (l) (left) (right))) ”
  &&  emp
).

Definition maxAreaLinear_entail_wit_2_1_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth left l 0) ) > maximumArea)) (PreH2 : ((Znth left l 0) < (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (LinearContainerTwoPointerInvariant l left right ((right - left ) * (Znth left l 0) ) )
.

Definition maxAreaLinear_entail_wit_2_1_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth left l 0) ) > maximumArea)) (PreH2 : ((Znth left l 0) < (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (((right - left ) * (Znth left l 0) ) <= 999990000)
.

Definition maxAreaLinear_entail_wit_2_1_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth left l 0) ) > maximumArea)) (PreH2 : ((Znth left l 0) < (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (((right - left ) * (Znth left l 0) ) = (LinearContainerArea (l) (left) (right)))
.

Definition maxAreaLinear_entail_wit_2_1_split_goal_4 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth left l 0) ) > maximumArea)) (PreH2 : ((Znth left l 0) < (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  ((Znth left l 0) <= 10000)
.

Definition maxAreaLinear_entail_wit_2_1_split_goal_5 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth left l 0) ) > maximumArea)) (PreH2 : ((Znth left l 0) < (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (0 <= (Znth left l 0))
.

Definition maxAreaLinear_entail_wit_2_1_split_goal_6 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth left l 0) ) > maximumArea)) (PreH2 : ((Znth left l 0) < (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  ((Znth left l 0) = (LinearContainerHeight (l) (left) (right)))
.

Definition maxAreaLinear_entail_wit_2_2 := 
(
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth right l 0) ) > maximumArea)) (PreH2 : ((Znth left l 0) >= (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
|--
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < right) ” 
  &&  “ (right < heightSize_pre) ” 
  &&  “ ((right - left ) = (right - left )) ” 
  &&  “ (1 <= (right - left )) ” 
  &&  “ ((right - left ) <= 99999) ” 
  &&  “ ((Znth right l 0) = (LinearContainerHeight (l) (left) (right))) ” 
  &&  “ (0 <= (Znth right l 0)) ” 
  &&  “ ((Znth right l 0) <= 10000) ” 
  &&  “ (((right - left ) * (Znth right l 0) ) = (LinearContainerArea (l) (left) (right))) ” 
  &&  “ (0 <= ((right - left ) * (Znth right l 0) )) ” 
  &&  “ (((right - left ) * (Znth right l 0) ) <= ((right - left ) * (Znth right l 0) )) ” 
  &&  “ (0 <= ((right - left ) * (Znth right l 0) )) ” 
  &&  “ (((right - left ) * (Znth right l 0) ) <= 999990000) ” 
  &&  “ (LinearContainerTwoPointerInvariant l left right ((right - left ) * (Znth right l 0) ) ) ” 
  &&  “ (Forall (Z.le (0)) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (IntArray.full height_pre heightSize_pre l )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth right l 0) ) > maximumArea)) (PreH2 : ((Znth left l 0) >= (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  TT && emp 
|--
  “ (LinearContainerTwoPointerInvariant l left right ((right - left ) * (Znth right l 0) ) ) ” 
  &&  “ (((right - left ) * (Znth right l 0) ) <= 999990000) ” 
  &&  “ (((right - left ) * (Znth right l 0) ) = (LinearContainerArea (l) (left) (right))) ” 
  &&  “ ((Znth right l 0) <= 10000) ” 
  &&  “ (0 <= (Znth right l 0)) ” 
  &&  “ ((Znth right l 0) = (LinearContainerHeight (l) (left) (right))) ”
  &&  emp
).

Definition maxAreaLinear_entail_wit_2_2_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth right l 0) ) > maximumArea)) (PreH2 : ((Znth left l 0) >= (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (LinearContainerTwoPointerInvariant l left right ((right - left ) * (Znth right l 0) ) )
.

Definition maxAreaLinear_entail_wit_2_2_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth right l 0) ) > maximumArea)) (PreH2 : ((Znth left l 0) >= (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (((right - left ) * (Znth right l 0) ) <= 999990000)
.

Definition maxAreaLinear_entail_wit_2_2_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth right l 0) ) > maximumArea)) (PreH2 : ((Znth left l 0) >= (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (((right - left ) * (Znth right l 0) ) = (LinearContainerArea (l) (left) (right)))
.

Definition maxAreaLinear_entail_wit_2_2_split_goal_4 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth right l 0) ) > maximumArea)) (PreH2 : ((Znth left l 0) >= (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  ((Znth right l 0) <= 10000)
.

Definition maxAreaLinear_entail_wit_2_2_split_goal_5 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth right l 0) ) > maximumArea)) (PreH2 : ((Znth left l 0) >= (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (0 <= (Znth right l 0))
.

Definition maxAreaLinear_entail_wit_2_2_split_goal_6 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth right l 0) ) > maximumArea)) (PreH2 : ((Znth left l 0) >= (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  ((Znth right l 0) = (LinearContainerHeight (l) (left) (right)))
.

Definition maxAreaLinear_entail_wit_2_3 := 
(
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth left l 0) ) <= maximumArea)) (PreH2 : ((Znth left l 0) < (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
|--
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < right) ” 
  &&  “ (right < heightSize_pre) ” 
  &&  “ ((right - left ) = (right - left )) ” 
  &&  “ (1 <= (right - left )) ” 
  &&  “ ((right - left ) <= 99999) ” 
  &&  “ ((Znth left l 0) = (LinearContainerHeight (l) (left) (right))) ” 
  &&  “ (0 <= (Znth left l 0)) ” 
  &&  “ ((Znth left l 0) <= 10000) ” 
  &&  “ (((right - left ) * (Znth left l 0) ) = (LinearContainerArea (l) (left) (right))) ” 
  &&  “ (0 <= ((right - left ) * (Znth left l 0) )) ” 
  &&  “ (((right - left ) * (Znth left l 0) ) <= maximumArea) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (LinearContainerTwoPointerInvariant l left right maximumArea ) ” 
  &&  “ (Forall (Z.le (0)) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (IntArray.full height_pre heightSize_pre l )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth left l 0) ) <= maximumArea)) (PreH2 : ((Znth left l 0) < (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  TT && emp 
|--
  “ (0 <= ((right - left ) * (Znth left l 0) )) ” 
  &&  “ (((right - left ) * (Znth left l 0) ) = (LinearContainerArea (l) (left) (right))) ” 
  &&  “ ((Znth left l 0) <= 10000) ” 
  &&  “ (0 <= (Znth left l 0)) ” 
  &&  “ ((Znth left l 0) = (LinearContainerHeight (l) (left) (right))) ”
  &&  emp
).

Definition maxAreaLinear_entail_wit_2_3_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth left l 0) ) <= maximumArea)) (PreH2 : ((Znth left l 0) < (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (0 <= ((right - left ) * (Znth left l 0) ))
.

Definition maxAreaLinear_entail_wit_2_3_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth left l 0) ) <= maximumArea)) (PreH2 : ((Znth left l 0) < (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (((right - left ) * (Znth left l 0) ) = (LinearContainerArea (l) (left) (right)))
.

Definition maxAreaLinear_entail_wit_2_3_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth left l 0) ) <= maximumArea)) (PreH2 : ((Znth left l 0) < (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  ((Znth left l 0) <= 10000)
.

Definition maxAreaLinear_entail_wit_2_3_split_goal_4 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth left l 0) ) <= maximumArea)) (PreH2 : ((Znth left l 0) < (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (0 <= (Znth left l 0))
.

Definition maxAreaLinear_entail_wit_2_3_split_goal_5 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth left l 0) ) <= maximumArea)) (PreH2 : ((Znth left l 0) < (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  ((Znth left l 0) = (LinearContainerHeight (l) (left) (right)))
.

Definition maxAreaLinear_entail_wit_2_4 := 
(
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth right l 0) ) <= maximumArea)) (PreH2 : ((Znth left l 0) >= (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
|--
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < right) ” 
  &&  “ (right < heightSize_pre) ” 
  &&  “ ((right - left ) = (right - left )) ” 
  &&  “ (1 <= (right - left )) ” 
  &&  “ ((right - left ) <= 99999) ” 
  &&  “ ((Znth right l 0) = (LinearContainerHeight (l) (left) (right))) ” 
  &&  “ (0 <= (Znth right l 0)) ” 
  &&  “ ((Znth right l 0) <= 10000) ” 
  &&  “ (((right - left ) * (Znth right l 0) ) = (LinearContainerArea (l) (left) (right))) ” 
  &&  “ (0 <= ((right - left ) * (Znth right l 0) )) ” 
  &&  “ (((right - left ) * (Znth right l 0) ) <= maximumArea) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (LinearContainerTwoPointerInvariant l left right maximumArea ) ” 
  &&  “ (Forall (Z.le (0)) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (IntArray.full height_pre heightSize_pre l )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth right l 0) ) <= maximumArea)) (PreH2 : ((Znth left l 0) >= (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  TT && emp 
|--
  “ (0 <= ((right - left ) * (Znth right l 0) )) ” 
  &&  “ (((right - left ) * (Znth right l 0) ) = (LinearContainerArea (l) (left) (right))) ” 
  &&  “ ((Znth right l 0) <= 10000) ” 
  &&  “ (0 <= (Znth right l 0)) ” 
  &&  “ ((Znth right l 0) = (LinearContainerHeight (l) (left) (right))) ”
  &&  emp
).

Definition maxAreaLinear_entail_wit_2_4_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth right l 0) ) <= maximumArea)) (PreH2 : ((Znth left l 0) >= (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (0 <= ((right - left ) * (Znth right l 0) ))
.

Definition maxAreaLinear_entail_wit_2_4_split_goal_2 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth right l 0) ) <= maximumArea)) (PreH2 : ((Znth left l 0) >= (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (((right - left ) * (Znth right l 0) ) = (LinearContainerArea (l) (left) (right)))
.

Definition maxAreaLinear_entail_wit_2_4_split_goal_3 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth right l 0) ) <= maximumArea)) (PreH2 : ((Znth left l 0) >= (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  ((Znth right l 0) <= 10000)
.

Definition maxAreaLinear_entail_wit_2_4_split_goal_4 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth right l 0) ) <= maximumArea)) (PreH2 : ((Znth left l 0) >= (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  (0 <= (Znth right l 0))
.

Definition maxAreaLinear_entail_wit_2_4_split_goal_5 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (((right - left ) * (Znth right l 0) ) <= maximumArea)) (PreH2 : ((Znth left l 0) >= (Znth right l 0))) (PreH3 : (left < right)) (PreH4 : (2 <= heightSize_pre)) (PreH5 : (heightSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = heightSize_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= right)) (PreH9 : (right < heightSize_pre)) (PreH10 : (0 <= maximumArea)) (PreH11 : (maximumArea <= 999990000)) (PreH12 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH13 : (Forall (Z.le (0)) l )) (PreH14 : (Forall (Z.ge (10000)) l )) ,
  ((Znth right l 0) = (LinearContainerHeight (l) (left) (right)))
.

Definition maxAreaLinear_entail_wit_3_1 := 
(
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (left: Z) (right: Z) (width: Z) (shorterHeight: Z) (area: Z) (maximumArea: Z) (PreH1 : ((Znth left l 0) < (Znth right l 0))) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= left)) (PreH6 : (left < right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (width = (right - left ))) (PreH9 : (1 <= width)) (PreH10 : (width <= 99999)) (PreH11 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH12 : (0 <= shorterHeight)) (PreH13 : (shorterHeight <= 10000)) (PreH14 : (area = (LinearContainerArea (l) (left) (right)))) (PreH15 : (0 <= area)) (PreH16 : (area <= maximumArea)) (PreH17 : (0 <= maximumArea)) (PreH18 : (maximumArea <= 999990000)) (PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH20 : (Forall (Z.le (0)) l )) (PreH21 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
|--
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (0 <= (left + 1 )) ” 
  &&  “ ((left + 1 ) <= right) ” 
  &&  “ (right < heightSize_pre) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (LinearContainerTwoPointerInvariant l (left + 1 ) right maximumArea ) ” 
  &&  “ (Forall (Z.le (0)) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (IntArray.full height_pre heightSize_pre l )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (left: Z) (right: Z) (width: Z) (shorterHeight: Z) (area: Z) (maximumArea: Z) (PreH1 : ((Znth left l 0) < (Znth right l 0))) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= left)) (PreH6 : (left < right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (width = (right - left ))) (PreH9 : (1 <= width)) (PreH10 : (width <= 99999)) (PreH11 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH12 : (0 <= shorterHeight)) (PreH13 : (shorterHeight <= 10000)) (PreH14 : (area = (LinearContainerArea (l) (left) (right)))) (PreH15 : (0 <= area)) (PreH16 : (area <= maximumArea)) (PreH17 : (0 <= maximumArea)) (PreH18 : (maximumArea <= 999990000)) (PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH20 : (Forall (Z.le (0)) l )) (PreH21 : (Forall (Z.ge (10000)) l )) ,
  TT && emp 
|--
  “ (LinearContainerTwoPointerInvariant l (left + 1 ) right maximumArea ) ”
  &&  emp
).

Definition maxAreaLinear_entail_wit_3_1_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (left: Z) (right: Z) (width: Z) (shorterHeight: Z) (area: Z) (maximumArea: Z) (PreH1 : ((Znth left l 0) < (Znth right l 0))) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= left)) (PreH6 : (left < right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (width = (right - left ))) (PreH9 : (1 <= width)) (PreH10 : (width <= 99999)) (PreH11 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH12 : (0 <= shorterHeight)) (PreH13 : (shorterHeight <= 10000)) (PreH14 : (area = (LinearContainerArea (l) (left) (right)))) (PreH15 : (0 <= area)) (PreH16 : (area <= maximumArea)) (PreH17 : (0 <= maximumArea)) (PreH18 : (maximumArea <= 999990000)) (PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH20 : (Forall (Z.le (0)) l )) (PreH21 : (Forall (Z.ge (10000)) l )) ,
  (LinearContainerTwoPointerInvariant l (left + 1 ) right maximumArea )
.

Definition maxAreaLinear_entail_wit_3_2 := 
(
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (left: Z) (right: Z) (width: Z) (shorterHeight: Z) (area: Z) (maximumArea: Z) (PreH1 : ((Znth left l 0) >= (Znth right l 0))) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= left)) (PreH6 : (left < right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (width = (right - left ))) (PreH9 : (1 <= width)) (PreH10 : (width <= 99999)) (PreH11 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH12 : (0 <= shorterHeight)) (PreH13 : (shorterHeight <= 10000)) (PreH14 : (area = (LinearContainerArea (l) (left) (right)))) (PreH15 : (0 <= area)) (PreH16 : (area <= maximumArea)) (PreH17 : (0 <= maximumArea)) (PreH18 : (maximumArea <= 999990000)) (PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH20 : (Forall (Z.le (0)) l )) (PreH21 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
|--
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= (right - 1 )) ” 
  &&  “ ((right - 1 ) < heightSize_pre) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (LinearContainerTwoPointerInvariant l left (right - 1 ) maximumArea ) ” 
  &&  “ (Forall (Z.le (0)) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (IntArray.full height_pre heightSize_pre l )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (left: Z) (right: Z) (width: Z) (shorterHeight: Z) (area: Z) (maximumArea: Z) (PreH1 : ((Znth left l 0) >= (Znth right l 0))) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= left)) (PreH6 : (left < right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (width = (right - left ))) (PreH9 : (1 <= width)) (PreH10 : (width <= 99999)) (PreH11 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH12 : (0 <= shorterHeight)) (PreH13 : (shorterHeight <= 10000)) (PreH14 : (area = (LinearContainerArea (l) (left) (right)))) (PreH15 : (0 <= area)) (PreH16 : (area <= maximumArea)) (PreH17 : (0 <= maximumArea)) (PreH18 : (maximumArea <= 999990000)) (PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH20 : (Forall (Z.le (0)) l )) (PreH21 : (Forall (Z.ge (10000)) l )) ,
  TT && emp 
|--
  “ (LinearContainerTwoPointerInvariant l left (right - 1 ) maximumArea ) ”
  &&  emp
).

Definition maxAreaLinear_entail_wit_3_2_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (left: Z) (right: Z) (width: Z) (shorterHeight: Z) (area: Z) (maximumArea: Z) (PreH1 : ((Znth left l 0) >= (Znth right l 0))) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= left)) (PreH6 : (left < right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (width = (right - left ))) (PreH9 : (1 <= width)) (PreH10 : (width <= 99999)) (PreH11 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH12 : (0 <= shorterHeight)) (PreH13 : (shorterHeight <= 10000)) (PreH14 : (area = (LinearContainerArea (l) (left) (right)))) (PreH15 : (0 <= area)) (PreH16 : (area <= maximumArea)) (PreH17 : (0 <= maximumArea)) (PreH18 : (maximumArea <= 999990000)) (PreH19 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH20 : (Forall (Z.le (0)) l )) (PreH21 : (Forall (Z.ge (10000)) l )) ,
  (LinearContainerTwoPointerInvariant l left (right - 1 ) maximumArea )
.

Definition maxAreaLinear_return_wit_1 := 
(
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (left >= right)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= left)) (PreH6 : (left <= right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (0 <= maximumArea)) (PreH9 : (maximumArea <= 999990000)) (PreH10 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH11 : (Forall (Z.le (0)) l )) (PreH12 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
|--
  “ (MaximumContainerArea l maximumArea ) ”
  &&  (IntArray.full height_pre heightSize_pre l )
) \/
(
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (left >= right)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= left)) (PreH6 : (left <= right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (0 <= maximumArea)) (PreH9 : (maximumArea <= 999990000)) (PreH10 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH11 : (Forall (Z.le (0)) l )) (PreH12 : (Forall (Z.ge (10000)) l )) ,
  TT && emp 
|--
  “ (MaximumContainerArea l maximumArea ) ”
  &&  emp
).

Definition maxAreaLinear_return_wit_1_split_goal_1 := 
forall (heightSize_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (left >= right)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= left)) (PreH6 : (left <= right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (0 <= maximumArea)) (PreH9 : (maximumArea <= 999990000)) (PreH10 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH11 : (Forall (Z.le (0)) l )) (PreH12 : (Forall (Z.ge (10000)) l )) ,
  (MaximumContainerArea l maximumArea )
.

Definition maxAreaLinear_partial_solve_wit_1 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (left < right)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= left)) (PreH6 : (left <= right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (0 <= maximumArea)) (PreH9 : (maximumArea <= 999990000)) (PreH10 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH11 : (Forall (Z.le (0)) l )) (PreH12 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
|--
  “ (left < right) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= right) ” 
  &&  “ (right < heightSize_pre) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (LinearContainerTwoPointerInvariant l left right maximumArea ) ” 
  &&  “ (Forall (Z.le (0)) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (((height_pre + (left * sizeof(INT)))) # Int  |-> (Znth left l 0))
  **  (IntArray.missing_i height_pre left 0 heightSize_pre l )
.

Definition maxAreaLinear_partial_solve_wit_2 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : (left < right)) (PreH2 : (2 <= heightSize_pre)) (PreH3 : (heightSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = heightSize_pre)) (PreH5 : (0 <= left)) (PreH6 : (left <= right)) (PreH7 : (right < heightSize_pre)) (PreH8 : (0 <= maximumArea)) (PreH9 : (maximumArea <= 999990000)) (PreH10 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH11 : (Forall (Z.le (0)) l )) (PreH12 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
|--
  “ (left < right) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= right) ” 
  &&  “ (right < heightSize_pre) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (LinearContainerTwoPointerInvariant l left right maximumArea ) ” 
  &&  “ (Forall (Z.le (0)) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (((height_pre + (right * sizeof(INT)))) # Int  |-> (Znth right l 0))
  **  (IntArray.missing_i height_pre right 0 heightSize_pre l )
.

Definition maxAreaLinear_partial_solve_wit_3 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : ((Znth left l 0) < (Znth right l 0))) (PreH2 : (left < right)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= right)) (PreH8 : (right < heightSize_pre)) (PreH9 : (0 <= maximumArea)) (PreH10 : (maximumArea <= 999990000)) (PreH11 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH12 : (Forall (Z.le (0)) l )) (PreH13 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
|--
  “ ((Znth left l 0) < (Znth right l 0)) ” 
  &&  “ (left < right) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= right) ” 
  &&  “ (right < heightSize_pre) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (LinearContainerTwoPointerInvariant l left right maximumArea ) ” 
  &&  “ (Forall (Z.le (0)) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (((height_pre + (left * sizeof(INT)))) # Int  |-> (Znth left l 0))
  **  (IntArray.missing_i height_pre left 0 heightSize_pre l )
.

Definition maxAreaLinear_partial_solve_wit_4 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (maximumArea: Z) (right: Z) (left: Z) (PreH1 : ((Znth left l 0) >= (Znth right l 0))) (PreH2 : (left < right)) (PreH3 : (2 <= heightSize_pre)) (PreH4 : (heightSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = heightSize_pre)) (PreH6 : (0 <= left)) (PreH7 : (left <= right)) (PreH8 : (right < heightSize_pre)) (PreH9 : (0 <= maximumArea)) (PreH10 : (maximumArea <= 999990000)) (PreH11 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH12 : (Forall (Z.le (0)) l )) (PreH13 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
|--
  “ ((Znth left l 0) >= (Znth right l 0)) ” 
  &&  “ (left < right) ” 
  &&  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left <= right) ” 
  &&  “ (right < heightSize_pre) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (LinearContainerTwoPointerInvariant l left right maximumArea ) ” 
  &&  “ (Forall (Z.le (0)) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (((height_pre + (right * sizeof(INT)))) # Int  |-> (Znth right l 0))
  **  (IntArray.missing_i height_pre right 0 heightSize_pre l )
.

Definition maxAreaLinear_partial_solve_wit_5 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (left: Z) (right: Z) (width: Z) (shorterHeight: Z) (area: Z) (maximumArea: Z) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (0 <= left)) (PreH5 : (left < right)) (PreH6 : (right < heightSize_pre)) (PreH7 : (width = (right - left ))) (PreH8 : (1 <= width)) (PreH9 : (width <= 99999)) (PreH10 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH11 : (0 <= shorterHeight)) (PreH12 : (shorterHeight <= 10000)) (PreH13 : (area = (LinearContainerArea (l) (left) (right)))) (PreH14 : (0 <= area)) (PreH15 : (area <= maximumArea)) (PreH16 : (0 <= maximumArea)) (PreH17 : (maximumArea <= 999990000)) (PreH18 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH19 : (Forall (Z.le (0)) l )) (PreH20 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
|--
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < right) ” 
  &&  “ (right < heightSize_pre) ” 
  &&  “ (width = (right - left )) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 99999) ” 
  &&  “ (shorterHeight = (LinearContainerHeight (l) (left) (right))) ” 
  &&  “ (0 <= shorterHeight) ” 
  &&  “ (shorterHeight <= 10000) ” 
  &&  “ (area = (LinearContainerArea (l) (left) (right))) ” 
  &&  “ (0 <= area) ” 
  &&  “ (area <= maximumArea) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (LinearContainerTwoPointerInvariant l left right maximumArea ) ” 
  &&  “ (Forall (Z.le (0)) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (((height_pre + (left * sizeof(INT)))) # Int  |-> (Znth left l 0))
  **  (IntArray.missing_i height_pre left 0 heightSize_pre l )
.

Definition maxAreaLinear_partial_solve_wit_6 := 
forall (heightSize_pre: Z) (height_pre: Z) (l: (@list Z)) (left: Z) (right: Z) (width: Z) (shorterHeight: Z) (area: Z) (maximumArea: Z) (PreH1 : (2 <= heightSize_pre)) (PreH2 : (heightSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = heightSize_pre)) (PreH4 : (0 <= left)) (PreH5 : (left < right)) (PreH6 : (right < heightSize_pre)) (PreH7 : (width = (right - left ))) (PreH8 : (1 <= width)) (PreH9 : (width <= 99999)) (PreH10 : (shorterHeight = (LinearContainerHeight (l) (left) (right)))) (PreH11 : (0 <= shorterHeight)) (PreH12 : (shorterHeight <= 10000)) (PreH13 : (area = (LinearContainerArea (l) (left) (right)))) (PreH14 : (0 <= area)) (PreH15 : (area <= maximumArea)) (PreH16 : (0 <= maximumArea)) (PreH17 : (maximumArea <= 999990000)) (PreH18 : (LinearContainerTwoPointerInvariant l left right maximumArea )) (PreH19 : (Forall (Z.le (0)) l )) (PreH20 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.full height_pre heightSize_pre l )
|--
  “ (2 <= heightSize_pre) ” 
  &&  “ (heightSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = heightSize_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < right) ” 
  &&  “ (right < heightSize_pre) ” 
  &&  “ (width = (right - left )) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 99999) ” 
  &&  “ (shorterHeight = (LinearContainerHeight (l) (left) (right))) ” 
  &&  “ (0 <= shorterHeight) ” 
  &&  “ (shorterHeight <= 10000) ” 
  &&  “ (area = (LinearContainerArea (l) (left) (right))) ” 
  &&  “ (0 <= area) ” 
  &&  “ (area <= maximumArea) ” 
  &&  “ (0 <= maximumArea) ” 
  &&  “ (maximumArea <= 999990000) ” 
  &&  “ (LinearContainerTwoPointerInvariant l left right maximumArea ) ” 
  &&  “ (Forall (Z.le (0)) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ”
  &&  (((height_pre + (right * sizeof(INT)))) # Int  |-> (Znth right l 0))
  **  (IntArray.missing_i height_pre right 0 heightSize_pre l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_maxAreaLinear_safety_wit_1 : maxAreaLinear_safety_wit_1.
Axiom proof_of_maxAreaLinear_safety_wit_2 : maxAreaLinear_safety_wit_2.
Axiom proof_of_maxAreaLinear_safety_wit_3 : maxAreaLinear_safety_wit_3.
Axiom proof_of_maxAreaLinear_safety_wit_4 : maxAreaLinear_safety_wit_4.
Axiom proof_of_maxAreaLinear_safety_wit_5 : maxAreaLinear_safety_wit_5.
Axiom proof_of_maxAreaLinear_safety_wit_6 : maxAreaLinear_safety_wit_6.
Axiom proof_of_maxAreaLinear_safety_wit_7 : maxAreaLinear_safety_wit_7.
Axiom proof_of_maxAreaLinear_safety_wit_8 : maxAreaLinear_safety_wit_8.
Axiom proof_of_maxAreaLinear_safety_wit_9 : maxAreaLinear_safety_wit_9.
Axiom proof_of_maxAreaLinear_safety_wit_10 : maxAreaLinear_safety_wit_10.
Axiom proof_of_maxAreaLinear_safety_wit_11 : maxAreaLinear_safety_wit_11.
Axiom proof_of_maxAreaLinear_safety_wit_12 : maxAreaLinear_safety_wit_12.
Axiom proof_of_maxAreaLinear_safety_wit_13 : maxAreaLinear_safety_wit_13.
Axiom proof_of_maxAreaLinear_entail_wit_1 : maxAreaLinear_entail_wit_1.
Axiom proof_of_maxAreaLinear_entail_wit_2_1 : maxAreaLinear_entail_wit_2_1.
Axiom proof_of_maxAreaLinear_entail_wit_2_2 : maxAreaLinear_entail_wit_2_2.
Axiom proof_of_maxAreaLinear_entail_wit_2_3 : maxAreaLinear_entail_wit_2_3.
Axiom proof_of_maxAreaLinear_entail_wit_2_4 : maxAreaLinear_entail_wit_2_4.
Axiom proof_of_maxAreaLinear_entail_wit_3_1 : maxAreaLinear_entail_wit_3_1.
Axiom proof_of_maxAreaLinear_entail_wit_3_2 : maxAreaLinear_entail_wit_3_2.
Axiom proof_of_maxAreaLinear_return_wit_1 : maxAreaLinear_return_wit_1.
Axiom proof_of_maxAreaLinear_partial_solve_wit_1 : maxAreaLinear_partial_solve_wit_1.
Axiom proof_of_maxAreaLinear_partial_solve_wit_2 : maxAreaLinear_partial_solve_wit_2.
Axiom proof_of_maxAreaLinear_partial_solve_wit_3 : maxAreaLinear_partial_solve_wit_3.
Axiom proof_of_maxAreaLinear_partial_solve_wit_4 : maxAreaLinear_partial_solve_wit_4.
Axiom proof_of_maxAreaLinear_partial_solve_wit_5 : maxAreaLinear_partial_solve_wit_5.
Axiom proof_of_maxAreaLinear_partial_solve_wit_6 : maxAreaLinear_partial_solve_wit_6.

End VC_Correct.
