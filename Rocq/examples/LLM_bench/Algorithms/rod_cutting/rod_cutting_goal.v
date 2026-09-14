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
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH4 : ((Znth 0 price_l 0) = 0)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "revenue" ) )) # Ptr  |-> revenue_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.undef_full revenue_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rod_cutting_safety_wit_2 := 
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH4 : ((Znth 0 price_l 0) = 0)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "revenue" ) )) # Ptr  |-> revenue_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.undef_full revenue_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rod_cutting_safety_wit_3 := 
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH4 : ((Znth 0 price_l 0) = 0)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) ,
  (((revenue_pre + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg revenue_pre 1 (n_pre + 1 ) )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "revenue" ) )) # Ptr  |-> revenue_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rod_cutting_safety_wit_4 := 
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (j: Z) (PreH1 : (j <= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH5 : ((Znth 0 price_l 0) = 0)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : ((Zlength (revenue_l)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l j )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 ))))) ,
  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "revenue" ) )) # Ptr  |-> revenue_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg revenue_pre 0 j revenue_l )
  **  (IntArray.undef_seg revenue_pre j (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rod_cutting_safety_wit_5 := 
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (j: Z) (PreH1 : (j <= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH5 : ((Znth 0 price_l 0) = 0)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : ((Zlength (revenue_l)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l j )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 ))))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |-> 0)
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "revenue" ) )) # Ptr  |-> revenue_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg revenue_pre 0 j revenue_l )
  **  (IntArray.undef_seg revenue_pre j (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rod_cutting_safety_wit_6 := 
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (0 <= (j - i ))) (PreH2 : ((j - i ) < j)) (PreH3 : (best <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (best >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i <= j)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH11 : ((Znth 0 price_l 0) = 0)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) (PreH13 : (1 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= (j + 1 ))) (PreH17 : (0 <= best)) (PreH18 : (best <= (j * 1000000 ))) (PreH19 : ((Zlength (revenue_l)) = j)) (PreH20 : (RodCutRevenueTable price_l revenue_l j )) (PreH21 : (RodCutScanBest price_l revenue_l j i best )) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 ))))) ,
  (IntArray.seg revenue_pre 0 j revenue_l )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "revenue" ) )) # Ptr  |-> revenue_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.undef_seg revenue_pre j (n_pre + 1 ) )
|--
  “ (((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l 0) )) ”
.

Definition rod_cutting_safety_wit_7 := 
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (0 <= (j - i ))) (PreH2 : ((j - i ) < j)) (PreH3 : (best <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (best >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i <= j)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH11 : ((Znth 0 price_l 0) = 0)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) (PreH13 : (1 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= (j + 1 ))) (PreH17 : (0 <= best)) (PreH18 : (best <= (j * 1000000 ))) (PreH19 : ((Zlength (revenue_l)) = j)) (PreH20 : (RodCutRevenueTable price_l revenue_l j )) (PreH21 : (RodCutScanBest price_l revenue_l j i best )) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 ))))) ,
  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "revenue" ) )) # Ptr  |-> revenue_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.seg revenue_pre 0 j revenue_l )
  **  (IntArray.undef_seg revenue_pre j (n_pre + 1 ) )
|--
  “ ((j - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - i )) ”
.

Definition rod_cutting_safety_wit_8 := 
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (best < ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l 0) ))) (PreH2 : (0 <= (j - i ))) (PreH3 : ((j - i ) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH12 : ((Znth 0 price_l 0) = 0)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1 ))) (PreH18 : (0 <= best)) (PreH19 : (best <= (j * 1000000 ))) (PreH20 : ((Zlength (revenue_l)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l j )) (PreH22 : (RodCutScanBest price_l revenue_l j i best )) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 ))))) ,
  (IntArray.seg revenue_pre 0 j revenue_l )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "revenue" ) )) # Ptr  |-> revenue_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "best" ) )) # Int  |-> ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l 0) ))
  **  (IntArray.undef_seg revenue_pre j (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition rod_cutting_safety_wit_9 := 
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (best >= ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l 0) ))) (PreH2 : (0 <= (j - i ))) (PreH3 : ((j - i ) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH12 : ((Znth 0 price_l 0) = 0)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1 ))) (PreH18 : (0 <= best)) (PreH19 : (best <= (j * 1000000 ))) (PreH20 : ((Zlength (revenue_l)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l j )) (PreH22 : (RodCutScanBest price_l revenue_l j i best )) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 ))))) ,
  (IntArray.seg revenue_pre 0 j revenue_l )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "revenue" ) )) # Ptr  |-> revenue_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.undef_seg revenue_pre j (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition rod_cutting_safety_wit_10 := 
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i > j)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH5 : ((Znth 0 price_l 0) = 0)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1 ))) (PreH11 : (0 <= best)) (PreH12 : (best <= (j * 1000000 ))) (PreH13 : ((Zlength (revenue_l)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l j )) (PreH15 : (RodCutScanBest price_l revenue_l j i best )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 ))))) ,
  (IntArray.seg revenue_pre 0 (j + 1 ) (app (revenue_l) ((cons (best) ((@nil Z))))) )
  **  (IntArray.undef_seg revenue_pre (j + 1 ) (n_pre + 1 ) )
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "revenue" ) )) # Ptr  |-> revenue_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition rod_cutting_entail_wit_1 := 
(
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH4 : ((Znth 0 price_l 0) = 0)) (PreH5 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (Znth k_3 price_l 0)) /\ ((Znth k_3 price_l 0) <= 1000000)))) ,
  (((revenue_pre + (0 * sizeof(INT)))) # Int  |-> 0)
  **  (IntArray.undef_seg revenue_pre 1 (n_pre + 1 ) )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
|--
  EX (revenue_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (price_l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth 0 price_l 0) = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (revenue_l)) = 1) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l 1 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 1)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 )))) ”
  &&  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg revenue_pre 0 1 revenue_l )
  **  (IntArray.undef_seg revenue_pre 1 (n_pre + 1 ) )
) \/
(
forall (n_pre: Z) (revenue_pre: Z) (price_l: (@list Z)) (PreH1 : (0 <= INT_MAX)) (PreH2 : (0 >= INT_MIN)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH6 : ((Znth 0 price_l 0) = 0)) (PreH7 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (Znth k_3 price_l 0)) /\ ((Znth k_3 price_l 0) <= 1000000)))) ,
  (((revenue_pre + (0 * sizeof(INT)))) # Int  |-> 0)
|--
  EX (revenue_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (price_l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth 0 price_l 0) = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (revenue_l)) = 1) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l 1 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 1)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 )))) ”
  &&  (IntArray.seg revenue_pre 0 1 revenue_l )
).

Definition rod_cutting_entail_wit_2 := 
(
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (j: Z) (PreH1 : (j <= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH5 : ((Znth 0 price_l 0) = 0)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (Znth k_3 price_l 0)) /\ ((Znth k_3 price_l 0) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < j)) -> ((0 <= (Znth k_4 revenue_l_2 0)) /\ ((Znth k_4 revenue_l_2 0) <= (k_4 * 1000000 ))))) ,
  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg revenue_pre 0 j revenue_l_2 )
  **  (IntArray.undef_seg revenue_pre j (n_pre + 1 ) )
|--
  EX (revenue_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (price_l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth 0 price_l 0) = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000))) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (j * 1000000 )) ” 
  &&  “ ((Zlength (revenue_l)) = j) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l j ) ” 
  &&  “ (RodCutScanBest price_l revenue_l j 1 0 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 )))) ”
  &&  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg revenue_pre 0 j revenue_l )
  **  (IntArray.undef_seg revenue_pre j (n_pre + 1 ) )
) \/
(
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (j: Z) (PreH1 : (j <= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH5 : ((Znth 0 price_l 0) = 0)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (Znth k_3 price_l 0)) /\ ((Znth k_3 price_l 0) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < j)) -> ((0 <= (Znth k_4 revenue_l_2 0)) /\ ((Znth k_4 revenue_l_2 0) <= (k_4 * 1000000 ))))) ,
  TT && emp 
|--
  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l_2 0)) /\ ((Znth k_2 revenue_l_2 0) <= (k_2 * 1000000 )))) ” 
  &&  “ (RodCutScanBest price_l revenue_l_2 j 1 0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000))) ”
  &&  emp
).

Definition rod_cutting_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (j: Z) (PreH1 : (j <= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH5 : ((Znth 0 price_l 0) = 0)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (Znth k_3 price_l 0)) /\ ((Znth k_3 price_l 0) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < j)) -> ((0 <= (Znth k_4 revenue_l_2 0)) /\ ((Znth k_4 revenue_l_2 0) <= (k_4 * 1000000 ))))) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l_2 0)) /\ ((Znth k_2 revenue_l_2 0) <= (k_2 * 1000000 ))))
.

Definition rod_cutting_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (j: Z) (PreH1 : (j <= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH5 : ((Znth 0 price_l 0) = 0)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (Znth k_3 price_l 0)) /\ ((Znth k_3 price_l 0) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < j)) -> ((0 <= (Znth k_4 revenue_l_2 0)) /\ ((Znth k_4 revenue_l_2 0) <= (k_4 * 1000000 ))))) ,
  (RodCutScanBest price_l revenue_l_2 j 1 0 )
.

Definition rod_cutting_entail_wit_2_split_goal_3 := 
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (j: Z) (PreH1 : (j <= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH5 : ((Znth 0 price_l 0) = 0)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (Znth k_3 price_l 0)) /\ ((Znth k_3 price_l 0) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < j)) -> ((0 <= (Znth k_4 revenue_l_2 0)) /\ ((Znth k_4 revenue_l_2 0) <= (k_4 * 1000000 ))))) ,
  forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))
.

Definition rod_cutting_entail_wit_3 := 
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i <= j)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH5 : ((Znth 0 price_l 0) = 0)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1 ))) (PreH11 : (0 <= best)) (PreH12 : (best <= (j * 1000000 ))) (PreH13 : ((Zlength (revenue_l)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l j )) (PreH15 : (RodCutScanBest price_l revenue_l j i best )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 ))))) ,
  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "revenue" ) )) # Ptr  |-> revenue_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg revenue_pre 0 j revenue_l )
  **  (IntArray.undef_seg revenue_pre j (n_pre + 1 ) )
|--
  “ (0 <= (j - i )) ” 
  &&  “ ((j - i ) < j) ” 
  &&  “ (best <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (best >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i <= j) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (price_l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth 0 price_l 0) = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000))) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= (j * 1000000 )) ” 
  &&  “ ((Zlength (revenue_l)) = j) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l j ) ” 
  &&  “ (RodCutScanBest price_l revenue_l j i best ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 )))) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "price" ) )) # Ptr  |-> price_pre)
  **  ((( &( "revenue" ) )) # Ptr  |-> revenue_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg revenue_pre 0 j revenue_l )
  **  (IntArray.undef_seg revenue_pre j (n_pre + 1 ) )
.

Definition rod_cutting_entail_wit_4_1 := 
(
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (best < ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ))) (PreH2 : (0 <= (j - i ))) (PreH3 : ((j - i ) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH12 : ((Znth 0 price_l 0) = 0)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1 ))) (PreH18 : (0 <= best)) (PreH19 : (best <= (j * 1000000 ))) (PreH20 : ((Zlength (revenue_l_2)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH22 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l_2 0)) /\ ((Znth k_2 revenue_l_2 0) <= (k_2 * 1000000 ))))) ,
  (IntArray.seg revenue_pre 0 j revenue_l_2 )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.undef_seg revenue_pre j (n_pre + 1 ) )
|--
  EX (revenue_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (price_l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth 0 price_l 0) = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000))) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (j + 1 )) ” 
  &&  “ (0 <= ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) )) ” 
  &&  “ (((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ) <= (j * 1000000 )) ” 
  &&  “ ((Zlength (revenue_l)) = j) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l j ) ” 
  &&  “ (RodCutScanBest price_l revenue_l j (i + 1 ) ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ) ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 )))) ”
  &&  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg revenue_pre 0 j revenue_l )
  **  (IntArray.undef_seg revenue_pre j (n_pre + 1 ) )
) \/
(
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (best < ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ))) (PreH2 : (0 <= (j - i ))) (PreH3 : ((j - i ) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH12 : ((Znth 0 price_l 0) = 0)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1 ))) (PreH18 : (0 <= best)) (PreH19 : (best <= (j * 1000000 ))) (PreH20 : ((Zlength (revenue_l_2)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH22 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l_2 0)) /\ ((Znth k_2 revenue_l_2 0) <= (k_2 * 1000000 ))))) ,
  TT && emp 
|--
  “ (RodCutScanBest price_l revenue_l_2 j (i + 1 ) ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ) ) ”
  &&  emp
).

Definition rod_cutting_entail_wit_4_1_split_goal_1 := 
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (best < ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ))) (PreH2 : (0 <= (j - i ))) (PreH3 : ((j - i ) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH12 : ((Znth 0 price_l 0) = 0)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1 ))) (PreH18 : (0 <= best)) (PreH19 : (best <= (j * 1000000 ))) (PreH20 : ((Zlength (revenue_l_2)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH22 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l_2 0)) /\ ((Znth k_2 revenue_l_2 0) <= (k_2 * 1000000 ))))) ,
  (RodCutScanBest price_l revenue_l_2 j (i + 1 ) ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ) )
.

Definition rod_cutting_entail_wit_4_2 := 
(
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (best >= ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ))) (PreH2 : (0 <= (j - i ))) (PreH3 : ((j - i ) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH12 : ((Znth 0 price_l 0) = 0)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1 ))) (PreH18 : (0 <= best)) (PreH19 : (best <= (j * 1000000 ))) (PreH20 : ((Zlength (revenue_l_2)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH22 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l_2 0)) /\ ((Znth k_2 revenue_l_2 0) <= (k_2 * 1000000 ))))) ,
  (IntArray.seg revenue_pre 0 j revenue_l_2 )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.undef_seg revenue_pre j (n_pre + 1 ) )
|--
  EX (revenue_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (price_l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth 0 price_l 0) = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000))) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (j + 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= (j * 1000000 )) ” 
  &&  “ ((Zlength (revenue_l)) = j) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l j ) ” 
  &&  “ (RodCutScanBest price_l revenue_l j (i + 1 ) best ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 )))) ”
  &&  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg revenue_pre 0 j revenue_l )
  **  (IntArray.undef_seg revenue_pre j (n_pre + 1 ) )
) \/
(
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (best >= ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ))) (PreH2 : (0 <= (j - i ))) (PreH3 : ((j - i ) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH12 : ((Znth 0 price_l 0) = 0)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1 ))) (PreH18 : (0 <= best)) (PreH19 : (best <= (j * 1000000 ))) (PreH20 : ((Zlength (revenue_l_2)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH22 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l_2 0)) /\ ((Znth k_2 revenue_l_2 0) <= (k_2 * 1000000 ))))) ,
  TT && emp 
|--
  “ (RodCutScanBest price_l revenue_l_2 j (i + 1 ) best ) ”
  &&  emp
).

Definition rod_cutting_entail_wit_4_2_split_goal_1 := 
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (best >= ((Znth i price_l 0) + (Znth ((j - i ) - 0 ) revenue_l_2 0) ))) (PreH2 : (0 <= (j - i ))) (PreH3 : ((j - i ) < j)) (PreH4 : (best <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (best >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i <= j)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH12 : ((Znth 0 price_l 0) = 0)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) (PreH14 : (1 <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (1 <= i)) (PreH17 : (i <= (j + 1 ))) (PreH18 : (0 <= best)) (PreH19 : (best <= (j * 1000000 ))) (PreH20 : ((Zlength (revenue_l_2)) = j)) (PreH21 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH22 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l_2 0)) /\ ((Znth k_2 revenue_l_2 0) <= (k_2 * 1000000 ))))) ,
  (RodCutScanBest price_l revenue_l_2 j (i + 1 ) best )
.

Definition rod_cutting_entail_wit_5 := 
(
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i > j)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH5 : ((Znth 0 price_l 0) = 0)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (Znth k_3 price_l 0)) /\ ((Znth k_3 price_l 0) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1 ))) (PreH11 : (0 <= best)) (PreH12 : (best <= (j * 1000000 ))) (PreH13 : ((Zlength (revenue_l_2)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH15 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < j)) -> ((0 <= (Znth k_4 revenue_l_2 0)) /\ ((Znth k_4 revenue_l_2 0) <= (k_4 * 1000000 ))))) ,
  (IntArray.seg revenue_pre 0 (j + 1 ) (app (revenue_l_2) ((cons (best) ((@nil Z))))) )
  **  (IntArray.undef_seg revenue_pre (j + 1 ) (n_pre + 1 ) )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
|--
  EX (revenue_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (price_l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth 0 price_l 0) = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000))) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (revenue_l)) = (j + 1 )) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l (j + 1 ) ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (j + 1 ))) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 )))) ”
  &&  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg revenue_pre 0 (j + 1 ) revenue_l )
  **  (IntArray.undef_seg revenue_pre (j + 1 ) (n_pre + 1 ) )
) \/
(
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i > j)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH5 : ((Znth 0 price_l 0) = 0)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (Znth k_3 price_l 0)) /\ ((Znth k_3 price_l 0) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1 ))) (PreH11 : (0 <= best)) (PreH12 : (best <= (j * 1000000 ))) (PreH13 : ((Zlength (revenue_l_2)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH15 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < j)) -> ((0 <= (Znth k_4 revenue_l_2 0)) /\ ((Znth k_4 revenue_l_2 0) <= (k_4 * 1000000 ))))) ,
  TT && emp 
|--
  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (j + 1 ))) -> ((0 <= (Znth k_2 (app (revenue_l_2) ((cons (best) ((@nil Z))))) 0)) /\ ((Znth k_2 (app (revenue_l_2) ((cons (best) ((@nil Z))))) 0) <= (k_2 * 1000000 )))) ” 
  &&  “ (RodCutRevenueTable price_l (app (revenue_l_2) ((cons (best) ((@nil Z))))) (j + 1 ) ) ” 
  &&  “ ((Zlength ((app (revenue_l_2) ((cons (best) ((@nil Z))))))) = (j + 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000))) ”
  &&  emp
).

Definition rod_cutting_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i > j)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH5 : ((Znth 0 price_l 0) = 0)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (Znth k_3 price_l 0)) /\ ((Znth k_3 price_l 0) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1 ))) (PreH11 : (0 <= best)) (PreH12 : (best <= (j * 1000000 ))) (PreH13 : ((Zlength (revenue_l_2)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH15 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < j)) -> ((0 <= (Znth k_4 revenue_l_2 0)) /\ ((Znth k_4 revenue_l_2 0) <= (k_4 * 1000000 ))))) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (j + 1 ))) -> ((0 <= (Znth k_2 (app (revenue_l_2) ((cons (best) ((@nil Z))))) 0)) /\ ((Znth k_2 (app (revenue_l_2) ((cons (best) ((@nil Z))))) 0) <= (k_2 * 1000000 ))))
.

Definition rod_cutting_entail_wit_5_split_goal_2 := 
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i > j)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH5 : ((Znth 0 price_l 0) = 0)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (Znth k_3 price_l 0)) /\ ((Znth k_3 price_l 0) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1 ))) (PreH11 : (0 <= best)) (PreH12 : (best <= (j * 1000000 ))) (PreH13 : ((Zlength (revenue_l_2)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH15 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < j)) -> ((0 <= (Znth k_4 revenue_l_2 0)) /\ ((Znth k_4 revenue_l_2 0) <= (k_4 * 1000000 ))))) ,
  (RodCutRevenueTable price_l (app (revenue_l_2) ((cons (best) ((@nil Z))))) (j + 1 ) )
.

Definition rod_cutting_entail_wit_5_split_goal_3 := 
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i > j)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH5 : ((Znth 0 price_l 0) = 0)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (Znth k_3 price_l 0)) /\ ((Znth k_3 price_l 0) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1 ))) (PreH11 : (0 <= best)) (PreH12 : (best <= (j * 1000000 ))) (PreH13 : ((Zlength (revenue_l_2)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH15 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < j)) -> ((0 <= (Znth k_4 revenue_l_2 0)) /\ ((Znth k_4 revenue_l_2 0) <= (k_4 * 1000000 ))))) ,
  ((Zlength ((app (revenue_l_2) ((cons (best) ((@nil Z))))))) = (j + 1 ))
.

Definition rod_cutting_entail_wit_5_split_goal_4 := 
forall (n_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i > j)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH5 : ((Znth 0 price_l 0) = 0)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= n_pre)) -> ((0 <= (Znth k_3 price_l 0)) /\ ((Znth k_3 price_l 0) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1 ))) (PreH11 : (0 <= best)) (PreH12 : (best <= (j * 1000000 ))) (PreH13 : ((Zlength (revenue_l_2)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH15 : (RodCutScanBest price_l revenue_l_2 j i best )) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < j)) -> ((0 <= (Znth k_4 revenue_l_2 0)) /\ ((Znth k_4 revenue_l_2 0) <= (k_4 * 1000000 ))))) ,
  forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))
.

Definition rod_cutting_return_wit_1 := 
(
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (j: Z) (PreH1 : (j > n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH5 : ((Znth 0 price_l 0) = 0)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 price_l 0)) /\ ((Znth k_2 price_l 0) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < j)) -> ((0 <= (Znth k_3 revenue_l_2 0)) /\ ((Znth k_3 revenue_l_2 0) <= (k_3 * 1000000 ))))) ,
  (IntArray.seg revenue_pre 0 j revenue_l_2 )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
|--
  EX (revenue_l: (@list Z)) ,
  “ ((Zlength (revenue_l)) = (n_pre + 1 )) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l (n_pre + 1 ) ) ” 
  &&  “ ((Znth (n_pre - 0 ) revenue_l_2 0) = (Znth n_pre revenue_l 0)) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 )))) ”
  &&  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.full revenue_pre (n_pre + 1 ) revenue_l )
) \/
(
forall (n_pre: Z) (revenue_pre: Z) (price_l: (@list Z)) (revenue_l_2: (@list Z)) (j: Z) (PreH1 : (j > n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH5 : ((Znth 0 price_l 0) = 0)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 <= n_pre)) -> ((0 <= (Znth k_2 price_l 0)) /\ ((Znth k_2 price_l 0) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : ((Zlength (revenue_l_2)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l_2 j )) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < j)) -> ((0 <= (Znth k_3 revenue_l_2 0)) /\ ((Znth k_3 revenue_l_2 0) <= (k_3 * 1000000 ))))) ,
  (IntArray.seg revenue_pre 0 j revenue_l_2 )
|--
  EX (revenue_l: (@list Z)) ,
  “ ((Zlength (revenue_l)) = (n_pre + 1 )) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l (n_pre + 1 ) ) ” 
  &&  “ ((Znth (n_pre - 0 ) revenue_l_2 0) = (Znth n_pre revenue_l 0)) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((0 <= (Znth k revenue_l 0)) /\ ((Znth k revenue_l 0) <= (k * 1000000 )))) ”
  &&  (IntArray.full revenue_pre (n_pre + 1 ) revenue_l )
).

Definition rod_cutting_partial_solve_wit_1 := 
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH4 : ((Znth 0 price_l 0) = 0)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) ,
  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.undef_full revenue_pre (n_pre + 1 ) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (price_l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth 0 price_l 0) = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000))) ”
  &&  (((revenue_pre + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg revenue_pre 1 (n_pre + 1 ) )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
.

Definition rod_cutting_partial_solve_wit_2 := 
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (0 <= (j - i ))) (PreH2 : ((j - i ) < j)) (PreH3 : (best <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (best >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i <= j)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH11 : ((Znth 0 price_l 0) = 0)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) (PreH13 : (1 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= (j + 1 ))) (PreH17 : (0 <= best)) (PreH18 : (best <= (j * 1000000 ))) (PreH19 : ((Zlength (revenue_l)) = j)) (PreH20 : (RodCutRevenueTable price_l revenue_l j )) (PreH21 : (RodCutScanBest price_l revenue_l j i best )) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 ))))) ,
  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg revenue_pre 0 j revenue_l )
  **  (IntArray.undef_seg revenue_pre j (n_pre + 1 ) )
|--
  “ (0 <= (j - i )) ” 
  &&  “ ((j - i ) < j) ” 
  &&  “ (best <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (best >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i <= j) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (price_l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth 0 price_l 0) = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000))) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= (j * 1000000 )) ” 
  &&  “ ((Zlength (revenue_l)) = j) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l j ) ” 
  &&  “ (RodCutScanBest price_l revenue_l j i best ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 )))) ”
  &&  (((price_pre + (i * sizeof(INT)))) # Int  |-> (Znth i price_l 0))
  **  (IntArray.missing_i price_pre i 0 (n_pre + 1 ) price_l )
  **  (IntArray.seg revenue_pre 0 j revenue_l )
  **  (IntArray.undef_seg revenue_pre j (n_pre + 1 ) )
.

Definition rod_cutting_partial_solve_wit_3 := 
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (0 <= (j - i ))) (PreH2 : ((j - i ) < j)) (PreH3 : (best <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (best >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i <= j)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH11 : ((Znth 0 price_l 0) = 0)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) (PreH13 : (1 <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= (j + 1 ))) (PreH17 : (0 <= best)) (PreH18 : (best <= (j * 1000000 ))) (PreH19 : ((Zlength (revenue_l)) = j)) (PreH20 : (RodCutRevenueTable price_l revenue_l j )) (PreH21 : (RodCutScanBest price_l revenue_l j i best )) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 ))))) ,
  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg revenue_pre 0 j revenue_l )
  **  (IntArray.undef_seg revenue_pre j (n_pre + 1 ) )
|--
  “ (0 <= (j - i )) ” 
  &&  “ ((j - i ) < j) ” 
  &&  “ (best <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (best >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i <= j) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (price_l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth 0 price_l 0) = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000))) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= (j * 1000000 )) ” 
  &&  “ ((Zlength (revenue_l)) = j) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l j ) ” 
  &&  “ (RodCutScanBest price_l revenue_l j i best ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 )))) ”
  &&  (((revenue_pre + ((j - i ) * sizeof(INT)))) # Int  |-> (Znth ((j - i ) - 0 ) revenue_l 0))
  **  (IntArray.missing_i revenue_pre (j - i ) 0 j revenue_l )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.undef_seg revenue_pre j (n_pre + 1 ) )
.

Definition rod_cutting_partial_solve_wit_4 := 
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (best: Z) (i: Z) (j: Z) (PreH1 : (i > j)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH5 : ((Znth 0 price_l 0) = 0)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (1 <= i)) (PreH10 : (i <= (j + 1 ))) (PreH11 : (0 <= best)) (PreH12 : (best <= (j * 1000000 ))) (PreH13 : ((Zlength (revenue_l)) = j)) (PreH14 : (RodCutRevenueTable price_l revenue_l j )) (PreH15 : (RodCutScanBest price_l revenue_l j i best )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 ))))) ,
  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg revenue_pre 0 j revenue_l )
  **  (IntArray.undef_seg revenue_pre j (n_pre + 1 ) )
|--
  “ (i > j) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (price_l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth 0 price_l 0) = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000))) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= (j * 1000000 )) ” 
  &&  “ ((Zlength (revenue_l)) = j) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l j ) ” 
  &&  “ (RodCutScanBest price_l revenue_l j i best ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 )))) ”
  &&  (((revenue_pre + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg revenue_pre (j + 1 ) (n_pre + 1 ) )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg revenue_pre 0 j revenue_l )
.

Definition rod_cutting_partial_solve_wit_5 := 
forall (n_pre: Z) (revenue_pre: Z) (price_pre: Z) (price_l: (@list Z)) (revenue_l: (@list Z)) (j: Z) (PreH1 : (j > n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (price_l)) = (n_pre + 1 ))) (PreH5 : ((Znth 0 price_l 0) = 0)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000)))) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : ((Zlength (revenue_l)) = j)) (PreH10 : (RodCutRevenueTable price_l revenue_l j )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 ))))) ,
  (IntArray.full price_pre (n_pre + 1 ) price_l )
  **  (IntArray.seg revenue_pre 0 j revenue_l )
  **  (IntArray.undef_seg revenue_pre j (n_pre + 1 ) )
|--
  “ (j > n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (price_l)) = (n_pre + 1 )) ” 
  &&  “ ((Znth 0 price_l 0) = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= n_pre)) -> ((0 <= (Znth k price_l 0)) /\ ((Znth k price_l 0) <= 1000000))) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (revenue_l)) = j) ” 
  &&  “ (RodCutRevenueTable price_l revenue_l j ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((0 <= (Znth k_2 revenue_l 0)) /\ ((Znth k_2 revenue_l 0) <= (k_2 * 1000000 )))) ”
  &&  (((revenue_pre + (n_pre * sizeof(INT)))) # Int  |-> (Znth (n_pre - 0 ) revenue_l 0))
  **  (IntArray.missing_i revenue_pre n_pre 0 j revenue_l )
  **  (IntArray.full price_pre (n_pre + 1 ) price_l )
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
Axiom proof_of_rod_cutting_entail_wit_3 : rod_cutting_entail_wit_3.
Axiom proof_of_rod_cutting_entail_wit_4_1 : rod_cutting_entail_wit_4_1.
Axiom proof_of_rod_cutting_entail_wit_4_2 : rod_cutting_entail_wit_4_2.
Axiom proof_of_rod_cutting_entail_wit_5 : rod_cutting_entail_wit_5.
Axiom proof_of_rod_cutting_return_wit_1 : rod_cutting_return_wit_1.
Axiom proof_of_rod_cutting_partial_solve_wit_1 : rod_cutting_partial_solve_wit_1.
Axiom proof_of_rod_cutting_partial_solve_wit_2 : rod_cutting_partial_solve_wit_2.
Axiom proof_of_rod_cutting_partial_solve_wit_3 : rod_cutting_partial_solve_wit_3.
Axiom proof_of_rod_cutting_partial_solve_wit_4 : rod_cutting_partial_solve_wit_4.
Axiom proof_of_rod_cutting_partial_solve_wit_5 : rod_cutting_partial_solve_wit_5.

End VC_Correct.
