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
Require Import SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_lib.
Local Open Scope sac.

(*----- Function rod_cutting -----*)

Definition rod_cutting_safety_wit_1 := 
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH4 : ((Znth 0 price_l 0) = 0)) (PreH5 : (Forall (Z.le (0)) price_l )) (PreH6 : (Forall (Z.ge (1000000)) price_l )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "revenue" ) ) 1001 )
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rod_cutting_safety_wit_2 := 
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH4 : ((Znth 0 price_l 0) = 0)) (PreH5 : (Forall (Z.le (0)) price_l )) (PreH6 : (Forall (Z.ge (1000000)) price_l )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "revenue" ) ) 1001 )
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rod_cutting_safety_wit_3 := 
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH4 : ((Znth 0 price_l 0) = 0)) (PreH5 : (Forall (Z.le (0)) price_l )) (PreH6 : (Forall (Z.ge (1000000)) price_l )) ,
  (((( &( "revenue" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "revenue" ) ) 1 1001 )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rod_cutting_safety_wit_4 := 
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (j: Z) (PreH1 : (j <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1 ))) (PreH7 : (RodCutRevenueTable price_l revenue_l j )) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 ))))) ,
  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rod_cutting_safety_wit_5 := 
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (j: Z) (PreH1 : (j <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1 ))) (PreH7 : (RodCutRevenueTable price_l revenue_l j )) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 ))))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |-> 0)
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rod_cutting_safety_wit_6 := 
(
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i <= j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= (j * 1000000 ))) (PreH11 : (RodCutRevenueTable price_l revenue_l j )) (PreH12 : (RodCutScanBest price_l revenue_l j i best )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 ))))) ,
  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
|--
  “ (((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l 0) )) ”
) \/
(
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i <= j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= (j * 1000000 ))) (PreH11 : (RodCutRevenueTable price_l revenue_l j )) (PreH12 : (RodCutScanBest price_l revenue_l j i best )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 ))))) ,
  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
|--
  “ (((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l 0) )) ”
).

Definition rod_cutting_safety_wit_6_split_goal_1 := 
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i <= j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= (j * 1000000 ))) (PreH11 : (RodCutRevenueTable price_l revenue_l j )) (PreH12 : (RodCutScanBest price_l revenue_l j i best )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 ))))) ,
  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
|--
  “ (((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l 0) ) <= INT_MAX) ”
.

Definition rod_cutting_safety_wit_6_split_goal_2 := 
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i <= j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= (j * 1000000 ))) (PreH11 : (RodCutRevenueTable price_l revenue_l j )) (PreH12 : (RodCutScanBest price_l revenue_l j i best )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 ))))) ,
  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
|--
  “ ((INT_MIN) <= ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l 0) )) ”
.

Definition rod_cutting_safety_wit_7 := 
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i <= j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= (j * 1000000 ))) (PreH11 : (RodCutRevenueTable price_l revenue_l j )) (PreH12 : (RodCutScanBest price_l revenue_l j i best )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 ))))) ,
  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
|--
  “ ((j - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - i )) ”
.

Definition rod_cutting_safety_wit_8 := 
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (best < ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l 0) ))) (PreH2 : (i <= j)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) price_l )) (PreH5 : (Forall (Z.ge (1000000)) price_l )) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : (1 <= i)) (PreH9 : (i <= (j + 1 ))) (PreH10 : (0 <= best)) (PreH11 : (best <= (j * 1000000 ))) (PreH12 : (RodCutRevenueTable price_l revenue_l j )) (PreH13 : (RodCutScanBest price_l revenue_l j i best )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 ))))) ,
  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l 0) ))
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition rod_cutting_safety_wit_9 := 
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (best >= ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l 0) ))) (PreH2 : (i <= j)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) price_l )) (PreH5 : (Forall (Z.ge (1000000)) price_l )) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : (1 <= i)) (PreH9 : (i <= (j + 1 ))) (PreH10 : (0 <= best)) (PreH11 : (best <= (j * 1000000 ))) (PreH12 : (RodCutRevenueTable price_l revenue_l j )) (PreH13 : (RodCutScanBest price_l revenue_l j i best )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 ))))) ,
  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition rod_cutting_safety_wit_10 := 
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i > j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= (j * 1000000 ))) (PreH11 : (RodCutRevenueTable price_l revenue_l j )) (PreH12 : (RodCutScanBest price_l revenue_l j i best )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 ))))) ,
  (IntArray.seg ( &( "revenue" ) ) 0 (j + 1 ) (app (revenue_l) ((cons (best) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "revenue" ) ) (j + 1 ) 1001 )
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition rod_cutting_entail_wit_1 := 
(
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH4 : ((Znth 0 price_l 0) = 0)) (PreH5 : (Forall (Z.le (0)) price_l )) (PreH6 : (Forall (Z.ge (1000000)) price_l )) ,
  (((( &( "revenue" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg ( &( "revenue" ) ) 1 1001 )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
|--
  EX (revenue_l: (@list Z)) ,
  “ (n_pre <= 1000) ” 
  &&  “ (Forall (Z.le (0)) price_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) price_l ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l 1 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 1)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 )))) ”
  &&  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg ( &( "revenue" ) ) 0 1 revenue_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) 1 1001 )
) \/
(
forall (n_pre: Z) (price_l: (@list Z)) (PreH1 : (0 <= INT_MAX)) (PreH2 : (0 >= INT_MIN)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH6 : ((Znth 0 price_l 0) = 0)) (PreH7 : (Forall (Z.le (0)) price_l )) (PreH8 : (Forall (Z.ge (1000000)) price_l )) ,
  (((( &( "revenue" ) ) + (0 * sizeof(INT)))) # Int  |-> 0)
|--
  EX (revenue_l: (@list Z)) ,
  “ (n_pre <= 1000) ” 
  &&  “ (Forall (Z.le (0)) price_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) price_l ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l 1 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 1)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 )))) ”
  &&  (IntArray.seg ( &( "revenue" ) ) 0 1 revenue_l )
).

Definition rod_cutting_entail_wit_2 := 
(
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (j: Z) (PreH1 : (j <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1 ))) (PreH7 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l_2 0)) /\ ((Znth k_2 revenue_l_2 0) <= (k_2 * 1000000 ))))) ,
  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l_2 )
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
|--
  EX (revenue_l: (@list Z)) ,
  “ (n_pre <= 1000) ” 
  &&  “ (Forall (Z.le (0)) price_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) price_l ) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (j * 1000000 )) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l j ) ” 
  &&  “ (RodCutScanBest price_l revenue_l j 1 0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 )))) ”
  &&  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
) \/
(
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (j: Z) (PreH1 : (j <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1 ))) (PreH7 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l_2 0)) /\ ((Znth k_2 revenue_l_2 0) <= (k_2 * 1000000 ))))) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l_2 0)) /\ ((Znth k revenue_l_2 0) <= (k * 1000000 )))) ” 
  &&  “ (RodCutScanBest price_l revenue_l_2 j 1 0 ) ”
  &&  emp
).

Definition rod_cutting_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (j: Z) (PreH1 : (j <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1 ))) (PreH7 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l_2 0)) /\ ((Znth k_2 revenue_l_2 0) <= (k_2 * 1000000 ))))) ,
  forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l_2 0)) /\ ((Znth k revenue_l_2 0) <= (k * 1000000 ))))
.

Definition rod_cutting_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (j: Z) (PreH1 : (j <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1 ))) (PreH7 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l_2 0)) /\ ((Znth k_2 revenue_l_2 0) <= (k_2 * 1000000 ))))) ,
  (RodCutScanBest price_l revenue_l_2 j 1 0 )
.

Definition rod_cutting_entail_wit_3_1 := 
(
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (best < ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ))) (PreH2 : (i <= j)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) price_l )) (PreH5 : (Forall (Z.ge (1000000)) price_l )) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : (1 <= i)) (PreH9 : (i <= (j + 1 ))) (PreH10 : (0 <= best)) (PreH11 : (best <= (j * 1000000 ))) (PreH12 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH13 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l_2 0)) /\ ((Znth k revenue_l_2 0) <= (k * 1000000 ))))) ,
  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l_2 )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
|--
  EX (revenue_l: (@list Z)) ,
  “ (n_pre <= 1000) ” 
  &&  “ (Forall (Z.le (0)) price_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) price_l ) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (j + 1 )) ” 
  &&  “ (0 <= ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) )) ” 
  &&  “ (((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ) <= (j * 1000000 )) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l j ) ” 
  &&  “ (RodCutScanBest price_l revenue_l j (i + 1 ) ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 )))) ”
  &&  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
) \/
(
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (best < ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ))) (PreH2 : (i <= j)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) price_l )) (PreH5 : (Forall (Z.ge (1000000)) price_l )) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : (1 <= i)) (PreH9 : (i <= (j + 1 ))) (PreH10 : (0 <= best)) (PreH11 : (best <= (j * 1000000 ))) (PreH12 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH13 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l_2 0)) /\ ((Znth k revenue_l_2 0) <= (k * 1000000 ))))) ,
  TT && emp 
|--
  “ (RodCutScanBest price_l revenue_l_2 j (i + 1 ) ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ) ) ” 
  &&  “ (((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ) <= (j * 1000000 )) ”
  &&  emp
).

Definition rod_cutting_entail_wit_3_1_split_goal_1 := 
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (best < ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ))) (PreH2 : (i <= j)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) price_l )) (PreH5 : (Forall (Z.ge (1000000)) price_l )) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : (1 <= i)) (PreH9 : (i <= (j + 1 ))) (PreH10 : (0 <= best)) (PreH11 : (best <= (j * 1000000 ))) (PreH12 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH13 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l_2 0)) /\ ((Znth k revenue_l_2 0) <= (k * 1000000 ))))) ,
  (RodCutScanBest price_l revenue_l_2 j (i + 1 ) ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ) )
.

Definition rod_cutting_entail_wit_3_1_split_goal_2 := 
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (best < ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ))) (PreH2 : (i <= j)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) price_l )) (PreH5 : (Forall (Z.ge (1000000)) price_l )) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : (1 <= i)) (PreH9 : (i <= (j + 1 ))) (PreH10 : (0 <= best)) (PreH11 : (best <= (j * 1000000 ))) (PreH12 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH13 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l_2 0)) /\ ((Znth k revenue_l_2 0) <= (k * 1000000 ))))) ,
  (((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ) <= (j * 1000000 ))
.

Definition rod_cutting_entail_wit_3_2 := 
(
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (best >= ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ))) (PreH2 : (i <= j)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) price_l )) (PreH5 : (Forall (Z.ge (1000000)) price_l )) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : (1 <= i)) (PreH9 : (i <= (j + 1 ))) (PreH10 : (0 <= best)) (PreH11 : (best <= (j * 1000000 ))) (PreH12 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH13 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l_2 0)) /\ ((Znth k revenue_l_2 0) <= (k * 1000000 ))))) ,
  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l_2 )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
|--
  EX (revenue_l: (@list Z)) ,
  “ (n_pre <= 1000) ” 
  &&  “ (Forall (Z.le (0)) price_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) price_l ) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (j + 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= (j * 1000000 )) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l j ) ” 
  &&  “ (RodCutScanBest price_l revenue_l j (i + 1 ) best ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 )))) ”
  &&  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
) \/
(
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (best >= ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ))) (PreH2 : (i <= j)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) price_l )) (PreH5 : (Forall (Z.ge (1000000)) price_l )) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : (1 <= i)) (PreH9 : (i <= (j + 1 ))) (PreH10 : (0 <= best)) (PreH11 : (best <= (j * 1000000 ))) (PreH12 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH13 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l_2 0)) /\ ((Znth k revenue_l_2 0) <= (k * 1000000 ))))) ,
  TT && emp 
|--
  “ (RodCutScanBest price_l revenue_l_2 j (i + 1 ) best ) ”
  &&  emp
).

Definition rod_cutting_entail_wit_3_2_split_goal_1 := 
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (best >= ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ))) (PreH2 : (i <= j)) (PreH3 : (n_pre <= 1000)) (PreH4 : (Forall (Z.le (0)) price_l )) (PreH5 : (Forall (Z.ge (1000000)) price_l )) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : (1 <= i)) (PreH9 : (i <= (j + 1 ))) (PreH10 : (0 <= best)) (PreH11 : (best <= (j * 1000000 ))) (PreH12 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH13 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l_2 0)) /\ ((Znth k revenue_l_2 0) <= (k * 1000000 ))))) ,
  (RodCutScanBest price_l revenue_l_2 j (i + 1 ) best )
.

Definition rod_cutting_entail_wit_4 := 
(
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i > j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= (j * 1000000 ))) (PreH11 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH12 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l_2 0)) /\ ((Znth k_2 revenue_l_2 0) <= (k_2 * 1000000 ))))) ,
  (IntArray.seg ( &( "revenue" ) ) 0 (j + 1 ) (app (revenue_l_2) ((cons (best) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "revenue" ) ) (j + 1 ) 1001 )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
|--
  EX (revenue_l: (@list Z)) ,
  “ (n_pre <= 1000) ” 
  &&  “ (Forall (Z.le (0)) price_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) price_l ) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l (j + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (j + 1 ))) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 )))) ”
  &&  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg ( &( "revenue" ) ) 0 (j + 1 ) revenue_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) (j + 1 ) 1001 )
) \/
(
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i > j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= (j * 1000000 ))) (PreH11 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH12 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l_2 0)) /\ ((Znth k_2 revenue_l_2 0) <= (k_2 * 1000000 ))))) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < (j + 1 ))) -> ((0 <= (Znth k (app (revenue_l_2) ((cons (best) ((@nil Z))))) 0)) /\ ((Znth k (app (revenue_l_2) ((cons (best) ((@nil Z))))) 0) <= (k * 1000000 )))) ” 
  &&  “ (RodCutRevenueTable price_l (app (revenue_l_2) ((cons (best) ((@nil Z))))) (j + 1 ) ) ”
  &&  emp
).

Definition rod_cutting_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i > j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= (j * 1000000 ))) (PreH11 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH12 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l_2 0)) /\ ((Znth k_2 revenue_l_2 0) <= (k_2 * 1000000 ))))) ,
  forall (k: Z) , (((0 <= k) /\ (k < (j + 1 ))) -> ((0 <= (Znth k (app (revenue_l_2) ((cons (best) ((@nil Z))))) 0)) /\ ((Znth k (app (revenue_l_2) ((cons (best) ((@nil Z))))) 0) <= (k * 1000000 ))))
.

Definition rod_cutting_entail_wit_4_split_goal_2 := 
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i > j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= (j * 1000000 ))) (PreH11 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH12 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l_2 0)) /\ ((Znth k_2 revenue_l_2 0) <= (k_2 * 1000000 ))))) ,
  (RodCutRevenueTable price_l (app (revenue_l_2) ((cons (best) ((@nil Z))))) (j + 1 ) )
.

Definition rod_cutting_entail_wit_5 := 
(
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (j: Z) (PreH1 : (j > n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1 ))) (PreH7 : (RodCutRevenueTable price_l revenue_l j )) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 ))))) ,
  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
|--
  “ (j = (n_pre + 1 )) ” 
  &&  “ (RodCutOptimalRevenue price_l n_pre (Znth (n_pre - 0 ) revenue_l 0) ) ”
  &&  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.undef_full ( &( "revenue" ) ) 1001 )
) \/
(
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (j: Z) (PreH1 : (j > n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1 ))) (PreH7 : (RodCutRevenueTable price_l revenue_l j )) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 ))))) ,
  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
|--
  “ (RodCutOptimalRevenue price_l n_pre (Znth (n_pre - 0 ) revenue_l 0) ) ”
  &&  (IntArray.undef_full ( &( "revenue" ) ) 1001 )
).

Definition rod_cutting_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (j: Z) (PreH1 : (j > n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1 ))) (PreH7 : (RodCutRevenueTable price_l revenue_l j )) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 ))))) ,
  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
|--
  “ (RodCutOptimalRevenue price_l n_pre (Znth (n_pre - 0 ) revenue_l 0) ) ”
.

Definition rod_cutting_entail_wit_5_split_goal_spatial := 
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (j: Z) (PreH1 : (j > n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1 ))) (PreH7 : (RodCutRevenueTable price_l revenue_l j )) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 ))))) ,
  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
|--
  (IntArray.undef_full ( &( "revenue" ) ) 1001 )
.

Definition rod_cutting_return_wit_1 := 
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (j: Z) (result: Z) (PreH1 : (j = (n_pre + 1 ))) (PreH2 : (RodCutOptimalRevenue price_l n_pre result )) ,
  (IntArray.full price_pre (n_pre + 1 ) price_l )
|--
  “ (RodCutOptimalRevenue price_l n_pre result ) ”
  &&  (IntArray.full price_pre (n_pre + 1 ) price_l )
.

Definition rod_cutting_partial_solve_wit_1 := 
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH4 : ((Znth 0 price_l 0) = 0)) (PreH5 : (Forall (Z.le (0)) price_l )) (PreH6 : (Forall (Z.ge (1000000)) price_l )) ,
  (IntArray.undef_full ( &( "revenue" ) ) 1001 )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (price_l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth 0 price_l 0) = 0) ” 
  &&  “ (Forall (Z.le (0)) price_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) price_l ) ”
  &&  (((( &( "revenue" ) ) + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "revenue" ) ) 1 1001 )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
.

Definition rod_cutting_partial_solve_wit_2 := 
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i <= j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= (j * 1000000 ))) (PreH11 : (RodCutRevenueTable price_l revenue_l j )) (PreH12 : (RodCutScanBest price_l revenue_l j i best )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 ))))) ,
  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
|--
  “ (i <= j) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (Forall (Z.le (0)) price_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) price_l ) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= (j * 1000000 )) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l j ) ” 
  &&  “ (RodCutScanBest price_l revenue_l j i best ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 )))) ”
  &&  (((price_pre + (i * sizeof(INT)))) # Int  |-> (Znth i price_l 0))
  **  (IntArray.missing_i price_pre i 0 (n_pre + 1 ) price_l )
  **  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
.

Definition rod_cutting_partial_solve_wit_3 := 
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i <= j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= (j * 1000000 ))) (PreH11 : (RodCutRevenueTable price_l revenue_l j )) (PreH12 : (RodCutScanBest price_l revenue_l j i best )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 ))))) ,
  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
|--
  “ (i <= j) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (Forall (Z.le (0)) price_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) price_l ) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= (j * 1000000 )) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l j ) ” 
  &&  “ (RodCutScanBest price_l revenue_l j i best ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 )))) ”
  &&  (((( &( "revenue" ) ) + ((j - i ) * sizeof(INT)))) # Int  |-> (Znth ((j - i ) - 0 ) revenue_l 0))
  **  (IntArray.missing_i ( &( "revenue" ) ) (j - i ) 0 j revenue_l )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
.

Definition rod_cutting_partial_solve_wit_4 := 
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i > j)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (j + 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= (j * 1000000 ))) (PreH11 : (RodCutRevenueTable price_l revenue_l j )) (PreH12 : (RodCutScanBest price_l revenue_l j i best )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 ))))) ,
  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
|--
  “ (i > j) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (Forall (Z.le (0)) price_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) price_l ) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= (j * 1000000 )) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l j ) ” 
  &&  “ (RodCutScanBest price_l revenue_l j i best ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 )))) ”
  &&  (((( &( "revenue" ) ) + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "revenue" ) ) (j + 1 ) 1001 )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
.

Definition rod_cutting_partial_solve_wit_5 := 
forall (n_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (j: Z) (PreH1 : (j > n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (Forall (Z.le (0)) price_l )) (PreH4 : (Forall (Z.ge (1000000)) price_l )) (PreH5 : (1 <= j)) (PreH6 : (j <= (n_pre + 1 ))) (PreH7 : (RodCutRevenueTable price_l revenue_l j )) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 ))))) ,
  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg ( &( "revenue" ) ) 0 j revenue_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
|--
  “ (j > n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (Forall (Z.le (0)) price_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) price_l ) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < j)) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 )))) ”
  &&  (((( &( "revenue" ) ) + (n_pre * sizeof(INT)))) # Int  |-> (Znth (n_pre - 0 ) revenue_l 0))
  **  (IntArray.missing_i ( &( "revenue" ) ) n_pre 0 j revenue_l )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.undef_seg ( &( "revenue" ) ) j 1001 )
.

Module Type VC_Correct.


Axiom proof_of_rod_cutting_safety_wit_1 : rod_cutting_safety_wit_1.
Axiom proof_of_rod_cutting_safety_wit_2 : rod_cutting_safety_wit_2.
Axiom proof_of_rod_cutting_safety_wit_3 : rod_cutting_safety_wit_3.
Axiom proof_of_rod_cutting_safety_wit_4 : rod_cutting_safety_wit_4.
Axiom proof_of_rod_cutting_safety_wit_5 : rod_cutting_safety_wit_5.
Axiom proof_of_rod_cutting_safety_wit_6 : rod_cutting_safety_wit_6.
Axiom proof_of_rod_cutting_safety_wit_7 : rod_cutting_safety_wit_7.
Axiom proof_of_rod_cutting_safety_wit_8 : rod_cutting_safety_wit_8.
Axiom proof_of_rod_cutting_safety_wit_9 : rod_cutting_safety_wit_9.
Axiom proof_of_rod_cutting_safety_wit_10 : rod_cutting_safety_wit_10.
Axiom proof_of_rod_cutting_entail_wit_1 : rod_cutting_entail_wit_1.
Axiom proof_of_rod_cutting_entail_wit_2 : rod_cutting_entail_wit_2.
Axiom proof_of_rod_cutting_entail_wit_3_1 : rod_cutting_entail_wit_3_1.
Axiom proof_of_rod_cutting_entail_wit_3_2 : rod_cutting_entail_wit_3_2.
Axiom proof_of_rod_cutting_entail_wit_4 : rod_cutting_entail_wit_4.
Axiom proof_of_rod_cutting_entail_wit_5 : rod_cutting_entail_wit_5.
Axiom proof_of_rod_cutting_return_wit_1 : rod_cutting_return_wit_1.
Axiom proof_of_rod_cutting_partial_solve_wit_1 : rod_cutting_partial_solve_wit_1.
Axiom proof_of_rod_cutting_partial_solve_wit_2 : rod_cutting_partial_solve_wit_2.
Axiom proof_of_rod_cutting_partial_solve_wit_3 : rod_cutting_partial_solve_wit_3.
Axiom proof_of_rod_cutting_partial_solve_wit_4 : rod_cutting_partial_solve_wit_4.
Axiom proof_of_rod_cutting_partial_solve_wit_5 : rod_cutting_partial_solve_wit_5.

End VC_Correct.
