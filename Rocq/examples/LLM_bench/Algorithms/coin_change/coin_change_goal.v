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
Require Import SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib.
Local Open Scope sac.

(*----- Function coinChange -----*)

Definition coinChange_safety_wit_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (Forall (Z.le (1)) coins_l )) (PreH6 : (Forall (Z.ge (INT_MAX)) coins_l )) ,
  (IntArray.undef_full ( &( "dp" ) ) 100001 )
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition coinChange_safety_wit_2 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (Forall (Z.le (1)) coins_l )) (PreH6 : (Forall (Z.ge (INT_MAX)) coins_l )) ,
  (IntArray.undef_full ( &( "dp" ) ) 100001 )
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition coinChange_safety_wit_3 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (Forall (Z.le (1)) coins_l )) (PreH6 : (Forall (Z.ge (INT_MAX)) coins_l )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  (((( &( "dp" ) ) + (0 * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg ( &( "dp" ) ) 1 100001 )
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition coinChange_safety_wit_4 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (PreH1 : (j <= amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (1 <= j)) (PreH6 : (j <= (amount_pre + 1 ))) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (DpPrefixZeroed dp_l j )) ,
  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 j dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) j (amount_pre + 1 ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition coinChange_safety_wit_5 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (PreH1 : (j <= amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (1 <= j)) (PreH6 : (j <= (amount_pre + 1 ))) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (DpPrefixZeroed dp_l j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (j + 1 ) (app (dp_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) (amount_pre + 1 ) )
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition coinChange_safety_wit_6 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (PreH1 : (j > amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (1 <= j)) (PreH6 : (j <= (amount_pre + 1 ))) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (DpPrefixZeroed dp_l j )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 j dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) j (amount_pre + 1 ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition coinChange_safety_wit_7 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : (j <= amount_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (amount_pre <= 100000)) (PreH4 : (0 <= i)) (PreH5 : (i < coinsSize_pre)) (PreH6 : (Forall (Z.le (1)) coins_l )) (PreH7 : (coin = (Znth i coins_l 0))) (PreH8 : (1 <= coin)) (PreH9 : (coin <= amount_pre)) (PreH10 : (coin <= j)) (PreH11 : (j <= (amount_pre + 1 ))) (PreH12 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l j amount_pre )) ,
  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "coin" ) )) # Int  |-> coin)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ ((j - coin ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - coin )) ”
.

Definition coinChange_safety_wit_8 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : (j <= amount_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (amount_pre <= 100000)) (PreH4 : (0 <= i)) (PreH5 : (i < coinsSize_pre)) (PreH6 : (Forall (Z.le (1)) coins_l )) (PreH7 : (coin = (Znth i coins_l 0))) (PreH8 : (1 <= coin)) (PreH9 : (coin <= amount_pre)) (PreH10 : (coin <= j)) (PreH11 : (j <= (amount_pre + 1 ))) (PreH12 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l j amount_pre )) ,
  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "coin" ) )) # Int  |-> coin)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition coinChange_safety_wit_9 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : ((Znth (j - coin ) dp_l 0) <> 0)) (PreH2 : (j <= amount_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < coinsSize_pre)) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (coin = (Znth i coins_l 0))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= amount_pre)) (PreH11 : (coin <= j)) (PreH12 : (j <= (amount_pre + 1 ))) (PreH13 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l j amount_pre )) ,
  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "coin" ) )) # Int  |-> coin)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition coinChange_safety_wit_10 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : ((Znth (j - coin ) dp_l 0) <> 0)) (PreH2 : (j <= amount_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < coinsSize_pre)) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (coin = (Znth i coins_l 0))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= amount_pre)) (PreH11 : (coin <= j)) (PreH12 : (j <= (amount_pre + 1 ))) (PreH13 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l j amount_pre )) ,
  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) (replace_Znth (j) (1) (dp_l)) )
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "coin" ) )) # Int  |-> coin)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition coinChange_safety_wit_11 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : ((Znth (j - coin ) dp_l 0) = 0)) (PreH2 : (j <= amount_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < coinsSize_pre)) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (coin = (Znth i coins_l 0))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= amount_pre)) (PreH11 : (coin <= j)) (PreH12 : (j <= (amount_pre + 1 ))) (PreH13 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l j amount_pre )) ,
  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "coin" ) )) # Int  |-> coin)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition coinChange_safety_wit_12 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : (j > amount_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (amount_pre <= 100000)) (PreH4 : (0 <= i)) (PreH5 : (i < coinsSize_pre)) (PreH6 : (Forall (Z.le (1)) coins_l )) (PreH7 : (coin = (Znth i coins_l 0))) (PreH8 : (1 <= coin)) (PreH9 : (coin <= amount_pre)) (PreH10 : (coin <= j)) (PreH11 : (j <= (amount_pre + 1 ))) (PreH12 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l j amount_pre )) ,
  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition coinChange_safety_wit_13 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (i: Z) (PreH1 : ((Znth i coins_l 0) > amount_pre)) (PreH2 : (i < coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= coinsSize_pre)) (PreH8 : (Forall (Z.le (1)) coins_l )) (PreH9 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l (amount_pre + 1 ) )) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition coinChange_safety_wit_14 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (res: Z) (PreH1 : (0 <= res)) (PreH2 : (res <= amount_pre)) (PreH3 : (DpReachableTable coins_l dp_l (amount_pre + 1 ) )) (PreH4 : (NoReachableAbove coins_l amount_pre res )) ,
  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "res" ) )) # Int  |-> res)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition coinChange_safety_wit_15 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (res: Z) (PreH1 : (res > 0)) (PreH2 : (0 <= res)) (PreH3 : (res <= amount_pre)) (PreH4 : (DpReachableTable coins_l dp_l (amount_pre + 1 ) )) (PreH5 : (NoReachableAbove coins_l amount_pre res )) ,
  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "res" ) )) # Int  |-> res)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition coinChange_safety_wit_16 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (res: Z) (PreH1 : ((Znth res dp_l 0) = 0)) (PreH2 : (res > 0)) (PreH3 : (0 <= res)) (PreH4 : (res <= amount_pre)) (PreH5 : (DpReachableTable coins_l dp_l (amount_pre + 1 ) )) (PreH6 : (NoReachableAbove coins_l amount_pre res )) ,
  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "res" ) )) # Int  |-> res)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ ((res - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (res - 1 )) ”
.

Definition coinChange_entail_wit_1 := 
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (Forall (Z.le (1)) coins_l )) (PreH6 : (Forall (Z.ge (INT_MAX)) coins_l )) ,
  (((( &( "dp" ) ) + (0 * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg ( &( "dp" ) ) 1 100001 )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (amount_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) coins_l ) ” 
  &&  “ (DpPrefixZeroed dp_l 1 ) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 1 dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) 1 (amount_pre + 1 ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (PreH1 : (1 <= INT_MAX)) (PreH2 : (1 >= INT_MIN)) (PreH3 : (0 <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : (0 <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (Forall (Z.ge (INT_MAX)) coins_l )) ,
  (((( &( "dp" ) ) + (0 * sizeof(INT)))) # Int  |-> 1)
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (amount_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) coins_l ) ” 
  &&  “ (DpPrefixZeroed dp_l 1 ) ”
  &&  (IntArray.seg ( &( "dp" ) ) 0 1 dp_l )
).

Definition coinChange_entail_wit_2 := 
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (PreH1 : (j <= amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (1 <= j)) (PreH6 : (j <= (amount_pre + 1 ))) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (DpPrefixZeroed dp_l_2 j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (j + 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) (amount_pre + 1 ) )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (amount_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) coins_l ) ” 
  &&  “ (DpPrefixZeroed dp_l (j + 1 ) ) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 (j + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) (amount_pre + 1 ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (PreH1 : (j <= amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (1 <= j)) (PreH6 : (j <= (amount_pre + 1 ))) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (DpPrefixZeroed dp_l_2 j )) ,
  TT && emp 
|--
  “ (DpPrefixZeroed (app (dp_l_2) ((cons (0) ((@nil Z))))) (j + 1 ) ) ”
  &&  emp
).

Definition coinChange_entail_wit_2_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (PreH1 : (j <= amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (1 <= j)) (PreH6 : (j <= (amount_pre + 1 ))) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (DpPrefixZeroed dp_l_2 j )) ,
  (DpPrefixZeroed (app (dp_l_2) ((cons (0) ((@nil Z))))) (j + 1 ) )
.

Definition coinChange_entail_wit_3 := 
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (PreH1 : (j > amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (1 <= j)) (PreH6 : (j <= (amount_pre + 1 ))) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (DpPrefixZeroed dp_l_2 j )) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 j dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) j (amount_pre + 1 ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  EX (dp_l: (@list Z)) ,
  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= coinsSize_pre) ” 
  &&  “ (Forall (Z.le (1)) coins_l ) ” 
  &&  “ (DpReachableTable (sublist (0) (0) (coins_l)) dp_l (amount_pre + 1 ) ) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (PreH1 : (j > amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (1 <= j)) (PreH6 : (j <= (amount_pre + 1 ))) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (DpPrefixZeroed dp_l_2 j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 j dp_l_2 )
|--
  EX (dp_l: (@list Z)) ,
  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= coinsSize_pre) ” 
  &&  “ (Forall (Z.le (1)) coins_l ) ” 
  &&  “ (DpReachableTable (sublist (0) (0) (coins_l)) dp_l (amount_pre + 1 ) ) ”
  &&  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
).

Definition coinChange_entail_wit_4 := 
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : ((Znth i coins_l 0) <= amount_pre)) (PreH2 : (i < coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= coinsSize_pre)) (PreH8 : (Forall (Z.le (1)) coins_l )) (PreH9 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  EX (dp_l: (@list Z)) ,
  “ (coinsSize_pre <= 100000) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < coinsSize_pre) ” 
  &&  “ (Forall (Z.le (1)) coins_l ) ” 
  &&  “ ((Znth i coins_l 0) = (Znth i coins_l 0)) ” 
  &&  “ (1 <= (Znth i coins_l 0)) ” 
  &&  “ ((Znth i coins_l 0) <= amount_pre) ” 
  &&  “ ((Znth i coins_l 0) <= (Znth i coins_l 0)) ” 
  &&  “ ((Znth i coins_l 0) <= (amount_pre + 1 )) ” 
  &&  “ (DpCoinInnerProgress (sublist (0) (i) (coins_l)) (Znth i coins_l 0) dp_l (Znth i coins_l 0) amount_pre ) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : ((Znth i coins_l 0) <= amount_pre)) (PreH2 : (i < coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= coinsSize_pre)) (PreH8 : (Forall (Z.le (1)) coins_l )) (PreH9 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) ,
  TT && emp 
|--
  “ (DpCoinInnerProgress (sublist (0) (i) (coins_l)) (Znth i coins_l 0) dp_l_2 (Znth i coins_l 0) amount_pre ) ” 
  &&  “ (1 <= (Znth i coins_l 0)) ”
  &&  emp
).

Definition coinChange_entail_wit_4_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : ((Znth i coins_l 0) <= amount_pre)) (PreH2 : (i < coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= coinsSize_pre)) (PreH8 : (Forall (Z.le (1)) coins_l )) (PreH9 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) ,
  (DpCoinInnerProgress (sublist (0) (i) (coins_l)) (Znth i coins_l 0) dp_l_2 (Znth i coins_l 0) amount_pre )
.

Definition coinChange_entail_wit_4_split_goal_2 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : ((Znth i coins_l 0) <= amount_pre)) (PreH2 : (i < coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= coinsSize_pre)) (PreH8 : (Forall (Z.le (1)) coins_l )) (PreH9 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) ,
  (1 <= (Znth i coins_l 0))
.

Definition coinChange_entail_wit_5_1 := 
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : ((Znth (j - coin ) dp_l_2 0) <> 0)) (PreH2 : (j <= amount_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < coinsSize_pre)) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (coin = (Znth i coins_l 0))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= amount_pre)) (PreH11 : (coin <= j)) (PreH12 : (j <= (amount_pre + 1 ))) (PreH13 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 j amount_pre )) ,
  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) (replace_Znth (j) (1) (dp_l_2)) )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  EX (dp_l: (@list Z)) ,
  “ (coinsSize_pre <= 100000) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < coinsSize_pre) ” 
  &&  “ (Forall (Z.le (1)) coins_l ) ” 
  &&  “ (coin = (Znth i coins_l 0)) ” 
  &&  “ (1 <= coin) ” 
  &&  “ (coin <= amount_pre) ” 
  &&  “ (coin <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (amount_pre + 1 )) ” 
  &&  “ (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l (j + 1 ) amount_pre ) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : ((Znth (j - coin ) dp_l_2 0) <> 0)) (PreH2 : (j <= amount_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < coinsSize_pre)) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (coin = (Znth i coins_l 0))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= amount_pre)) (PreH11 : (coin <= j)) (PreH12 : (j <= (amount_pre + 1 ))) (PreH13 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 j amount_pre )) ,
  TT && emp 
|--
  “ (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin (replace_Znth (j) (1) (dp_l_2)) (j + 1 ) amount_pre ) ”
  &&  emp
).

Definition coinChange_entail_wit_5_1_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : ((Znth (j - coin ) dp_l_2 0) <> 0)) (PreH2 : (j <= amount_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < coinsSize_pre)) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (coin = (Znth i coins_l 0))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= amount_pre)) (PreH11 : (coin <= j)) (PreH12 : (j <= (amount_pre + 1 ))) (PreH13 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 j amount_pre )) ,
  (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin (replace_Znth (j) (1) (dp_l_2)) (j + 1 ) amount_pre )
.

Definition coinChange_entail_wit_5_2 := 
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : ((Znth (j - coin ) dp_l_2 0) = 0)) (PreH2 : (j <= amount_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < coinsSize_pre)) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (coin = (Znth i coins_l 0))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= amount_pre)) (PreH11 : (coin <= j)) (PreH12 : (j <= (amount_pre + 1 ))) (PreH13 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 j amount_pre )) ,
  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l_2 )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  EX (dp_l: (@list Z)) ,
  “ (coinsSize_pre <= 100000) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < coinsSize_pre) ” 
  &&  “ (Forall (Z.le (1)) coins_l ) ” 
  &&  “ (coin = (Znth i coins_l 0)) ” 
  &&  “ (1 <= coin) ” 
  &&  “ (coin <= amount_pre) ” 
  &&  “ (coin <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (amount_pre + 1 )) ” 
  &&  “ (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l (j + 1 ) amount_pre ) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : ((Znth (j - coin ) dp_l_2 0) = 0)) (PreH2 : (j <= amount_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < coinsSize_pre)) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (coin = (Znth i coins_l 0))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= amount_pre)) (PreH11 : (coin <= j)) (PreH12 : (j <= (amount_pre + 1 ))) (PreH13 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 j amount_pre )) ,
  TT && emp 
|--
  “ (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 (j + 1 ) amount_pre ) ”
  &&  emp
).

Definition coinChange_entail_wit_5_2_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : ((Znth (j - coin ) dp_l_2 0) = 0)) (PreH2 : (j <= amount_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < coinsSize_pre)) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (coin = (Znth i coins_l 0))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= amount_pre)) (PreH11 : (coin <= j)) (PreH12 : (j <= (amount_pre + 1 ))) (PreH13 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 j amount_pre )) ,
  (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 (j + 1 ) amount_pre )
.

Definition coinChange_entail_wit_6_1 := 
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : (j > amount_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (amount_pre <= 100000)) (PreH4 : (0 <= i)) (PreH5 : (i < coinsSize_pre)) (PreH6 : (Forall (Z.le (1)) coins_l )) (PreH7 : (coin = (Znth i coins_l 0))) (PreH8 : (1 <= coin)) (PreH9 : (coin <= amount_pre)) (PreH10 : (coin <= j)) (PreH11 : (j <= (amount_pre + 1 ))) (PreH12 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 j amount_pre )) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  EX (dp_l: (@list Z)) ,
  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= coinsSize_pre) ” 
  &&  “ (Forall (Z.le (1)) coins_l ) ” 
  &&  “ (DpReachableTable (sublist (0) ((i + 1 )) (coins_l)) dp_l (amount_pre + 1 ) ) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : (j > amount_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (amount_pre <= 100000)) (PreH4 : (0 <= i)) (PreH5 : (i < coinsSize_pre)) (PreH6 : (Forall (Z.le (1)) coins_l )) (PreH7 : (coin = (Znth i coins_l 0))) (PreH8 : (1 <= coin)) (PreH9 : (coin <= amount_pre)) (PreH10 : (coin <= j)) (PreH11 : (j <= (amount_pre + 1 ))) (PreH12 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 j amount_pre )) ,
  TT && emp 
|--
  “ (DpReachableTable (sublist (0) ((i + 1 )) (coins_l)) dp_l_2 (amount_pre + 1 ) ) ”
  &&  emp
).

Definition coinChange_entail_wit_6_1_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : (j > amount_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (amount_pre <= 100000)) (PreH4 : (0 <= i)) (PreH5 : (i < coinsSize_pre)) (PreH6 : (Forall (Z.le (1)) coins_l )) (PreH7 : (coin = (Znth i coins_l 0))) (PreH8 : (1 <= coin)) (PreH9 : (coin <= amount_pre)) (PreH10 : (coin <= j)) (PreH11 : (j <= (amount_pre + 1 ))) (PreH12 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 j amount_pre )) ,
  (DpReachableTable (sublist (0) ((i + 1 )) (coins_l)) dp_l_2 (amount_pre + 1 ) )
.

Definition coinChange_entail_wit_6_2 := 
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : ((Znth i coins_l 0) > amount_pre)) (PreH2 : (i < coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= coinsSize_pre)) (PreH8 : (Forall (Z.le (1)) coins_l )) (PreH9 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  EX (dp_l: (@list Z)) ,
  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= coinsSize_pre) ” 
  &&  “ (Forall (Z.le (1)) coins_l ) ” 
  &&  “ (DpReachableTable (sublist (0) ((i + 1 )) (coins_l)) dp_l (amount_pre + 1 ) ) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : ((Znth i coins_l 0) > amount_pre)) (PreH2 : (i < coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= coinsSize_pre)) (PreH8 : (Forall (Z.le (1)) coins_l )) (PreH9 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) ,
  TT && emp 
|--
  “ (DpReachableTable (sublist (0) ((i + 1 )) (coins_l)) dp_l_2 (amount_pre + 1 ) ) ”
  &&  emp
).

Definition coinChange_entail_wit_6_2_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : ((Znth i coins_l 0) > amount_pre)) (PreH2 : (i < coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= coinsSize_pre)) (PreH8 : (Forall (Z.le (1)) coins_l )) (PreH9 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) ,
  (DpReachableTable (sublist (0) ((i + 1 )) (coins_l)) dp_l_2 (amount_pre + 1 ) )
.

Definition coinChange_entail_wit_7 := 
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i >= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= coinsSize_pre)) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= amount_pre) ” 
  &&  “ (DpReachableTable coins_l dp_l (amount_pre + 1 ) ) ” 
  &&  “ (NoReachableAbove coins_l amount_pre amount_pre ) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i >= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= coinsSize_pre)) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) ,
  TT && emp 
|--
  “ (NoReachableAbove coins_l amount_pre amount_pre ) ” 
  &&  “ (DpReachableTable coins_l dp_l_2 (amount_pre + 1 ) ) ”
  &&  emp
).

Definition coinChange_entail_wit_7_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i >= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= coinsSize_pre)) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) ,
  (NoReachableAbove coins_l amount_pre amount_pre )
.

Definition coinChange_entail_wit_7_split_goal_2 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i >= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= coinsSize_pre)) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) ,
  (DpReachableTable coins_l dp_l_2 (amount_pre + 1 ) )
.

Definition coinChange_entail_wit_8 := 
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (res: Z) (PreH1 : ((Znth res dp_l_2 0) = 0)) (PreH2 : (res > 0)) (PreH3 : (0 <= res)) (PreH4 : (res <= amount_pre)) (PreH5 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1 ) )) (PreH6 : (NoReachableAbove coins_l amount_pre res )) ,
  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l_2 )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= (res - 1 )) ” 
  &&  “ ((res - 1 ) <= amount_pre) ” 
  &&  “ (DpReachableTable coins_l dp_l (amount_pre + 1 ) ) ” 
  &&  “ (NoReachableAbove coins_l amount_pre (res - 1 ) ) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
) \/
(
forall (amount_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (res: Z) (PreH1 : ((Znth res dp_l_2 0) = 0)) (PreH2 : (res > 0)) (PreH3 : (0 <= res)) (PreH4 : (res <= amount_pre)) (PreH5 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1 ) )) (PreH6 : (NoReachableAbove coins_l amount_pre res )) ,
  TT && emp 
|--
  “ (NoReachableAbove coins_l amount_pre (res - 1 ) ) ”
  &&  emp
).

Definition coinChange_entail_wit_8_split_goal_1 := 
forall (amount_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (res: Z) (PreH1 : ((Znth res dp_l_2 0) = 0)) (PreH2 : (res > 0)) (PreH3 : (0 <= res)) (PreH4 : (res <= amount_pre)) (PreH5 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1 ) )) (PreH6 : (NoReachableAbove coins_l amount_pre res )) ,
  (NoReachableAbove coins_l amount_pre (res - 1 ) )
.

Definition coinChange_entail_wit_9_1 := 
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (res: Z) (PreH1 : (res <= 0)) (PreH2 : (0 <= res)) (PreH3 : (res <= amount_pre)) (PreH4 : (DpReachableTable coins_l dp_l (amount_pre + 1 ) )) (PreH5 : (NoReachableAbove coins_l amount_pre res )) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ (MaxReachableAmount coins_l amount_pre res ) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_full ( &( "dp" ) ) 100001 )
) \/
(
forall (amount_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (res: Z) (PreH1 : (res <= 0)) (PreH2 : (0 <= res)) (PreH3 : (res <= amount_pre)) (PreH4 : (DpReachableTable coins_l dp_l (amount_pre + 1 ) )) (PreH5 : (NoReachableAbove coins_l amount_pre res )) ,
  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ (MaxReachableAmount coins_l amount_pre res ) ”
  &&  (IntArray.undef_full ( &( "dp" ) ) 100001 )
).

Definition coinChange_entail_wit_9_1_split_goal_1 := 
forall (amount_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (res: Z) (PreH1 : (res <= 0)) (PreH2 : (0 <= res)) (PreH3 : (res <= amount_pre)) (PreH4 : (DpReachableTable coins_l dp_l (amount_pre + 1 ) )) (PreH5 : (NoReachableAbove coins_l amount_pre res )) ,
  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ (MaxReachableAmount coins_l amount_pre res ) ”
.

Definition coinChange_entail_wit_9_1_split_goal_spatial := 
forall (amount_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (res: Z) (PreH1 : (res <= 0)) (PreH2 : (0 <= res)) (PreH3 : (res <= amount_pre)) (PreH4 : (DpReachableTable coins_l dp_l (amount_pre + 1 ) )) (PreH5 : (NoReachableAbove coins_l amount_pre res )) ,
  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  (IntArray.undef_full ( &( "dp" ) ) 100001 )
.

Definition coinChange_entail_wit_9_2 := 
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (res: Z) (PreH1 : ((Znth res dp_l 0) <> 0)) (PreH2 : (res > 0)) (PreH3 : (0 <= res)) (PreH4 : (res <= amount_pre)) (PreH5 : (DpReachableTable coins_l dp_l (amount_pre + 1 ) )) (PreH6 : (NoReachableAbove coins_l amount_pre res )) ,
  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ (MaxReachableAmount coins_l amount_pre res ) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_full ( &( "dp" ) ) 100001 )
) \/
(
forall (amount_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (res: Z) (PreH1 : ((Znth res dp_l 0) <> 0)) (PreH2 : (res > 0)) (PreH3 : (0 <= res)) (PreH4 : (res <= amount_pre)) (PreH5 : (DpReachableTable coins_l dp_l (amount_pre + 1 ) )) (PreH6 : (NoReachableAbove coins_l amount_pre res )) ,
  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ (MaxReachableAmount coins_l amount_pre res ) ”
  &&  (IntArray.undef_full ( &( "dp" ) ) 100001 )
).

Definition coinChange_entail_wit_9_2_split_goal_1 := 
forall (amount_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (res: Z) (PreH1 : ((Znth res dp_l 0) <> 0)) (PreH2 : (res > 0)) (PreH3 : (0 <= res)) (PreH4 : (res <= amount_pre)) (PreH5 : (DpReachableTable coins_l dp_l (amount_pre + 1 ) )) (PreH6 : (NoReachableAbove coins_l amount_pre res )) ,
  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ (MaxReachableAmount coins_l amount_pre res ) ”
.

Definition coinChange_entail_wit_9_2_split_goal_spatial := 
forall (amount_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (res: Z) (PreH1 : ((Znth res dp_l 0) <> 0)) (PreH2 : (res > 0)) (PreH3 : (0 <= res)) (PreH4 : (res <= amount_pre)) (PreH5 : (DpReachableTable coins_l dp_l (amount_pre + 1 ) )) (PreH6 : (NoReachableAbove coins_l amount_pre res )) ,
  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  (IntArray.undef_full ( &( "dp" ) ) 100001 )
.

Definition coinChange_return_wit_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (res: Z) (PreH1 : (MaxReachableAmount coins_l amount_pre res )) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
|--
  “ (MaxReachableAmount coins_l amount_pre res ) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
.

Definition coinChange_partial_solve_wit_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (Forall (Z.le (1)) coins_l )) (PreH6 : (Forall (Z.ge (INT_MAX)) coins_l )) ,
  (IntArray.undef_full ( &( "dp" ) ) 100001 )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
|--
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ (Forall (Z.le (1)) coins_l ) ” 
  &&  “ (Forall (Z.ge (INT_MAX)) coins_l ) ”
  &&  (((( &( "dp" ) ) + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) 1 100001 )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
.

Definition coinChange_partial_solve_wit_2 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (PreH1 : (j <= amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (1 <= j)) (PreH6 : (j <= (amount_pre + 1 ))) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (DpPrefixZeroed dp_l j )) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 j dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) j (amount_pre + 1 ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ (j <= amount_pre) ” 
  &&  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (amount_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) coins_l ) ” 
  &&  “ (DpPrefixZeroed dp_l j ) ”
  &&  (((( &( "dp" ) ) + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) (amount_pre + 1 ) )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 j dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
.

Definition coinChange_partial_solve_wit_3 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (i: Z) (PreH1 : (i < coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= coinsSize_pre)) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l (amount_pre + 1 ) )) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ (i < coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= coinsSize_pre) ” 
  &&  “ (Forall (Z.le (1)) coins_l ) ” 
  &&  “ (DpReachableTable (sublist (0) (i) (coins_l)) dp_l (amount_pre + 1 ) ) ”
  &&  (((coins_pre + (i * sizeof(INT)))) # Int  |-> (Znth i coins_l 0))
  **  (IntArray.missing_i coins_pre i 0 coinsSize_pre coins_l )
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
.

Definition coinChange_partial_solve_wit_4 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : (j <= amount_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (amount_pre <= 100000)) (PreH4 : (0 <= i)) (PreH5 : (i < coinsSize_pre)) (PreH6 : (Forall (Z.le (1)) coins_l )) (PreH7 : (coin = (Znth i coins_l 0))) (PreH8 : (1 <= coin)) (PreH9 : (coin <= amount_pre)) (PreH10 : (coin <= j)) (PreH11 : (j <= (amount_pre + 1 ))) (PreH12 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l j amount_pre )) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ (j <= amount_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < coinsSize_pre) ” 
  &&  “ (Forall (Z.le (1)) coins_l ) ” 
  &&  “ (coin = (Znth i coins_l 0)) ” 
  &&  “ (1 <= coin) ” 
  &&  “ (coin <= amount_pre) ” 
  &&  “ (coin <= j) ” 
  &&  “ (j <= (amount_pre + 1 )) ” 
  &&  “ (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l j amount_pre ) ”
  &&  (((( &( "dp" ) ) + ((j - coin ) * sizeof(INT)))) # Int  |-> (Znth (j - coin ) dp_l 0))
  **  (IntArray.missing_i ( &( "dp" ) ) (j - coin ) 0 (amount_pre + 1 ) dp_l )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
.

Definition coinChange_partial_solve_wit_5 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : ((Znth (j - coin ) dp_l 0) <> 0)) (PreH2 : (j <= amount_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (amount_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < coinsSize_pre)) (PreH7 : (Forall (Z.le (1)) coins_l )) (PreH8 : (coin = (Znth i coins_l 0))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= amount_pre)) (PreH11 : (coin <= j)) (PreH12 : (j <= (amount_pre + 1 ))) (PreH13 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l j amount_pre )) ,
  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ ((Znth (j - coin ) dp_l 0) <> 0) ” 
  &&  “ (j <= amount_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < coinsSize_pre) ” 
  &&  “ (Forall (Z.le (1)) coins_l ) ” 
  &&  “ (coin = (Znth i coins_l 0)) ” 
  &&  “ (1 <= coin) ” 
  &&  “ (coin <= amount_pre) ” 
  &&  “ (coin <= j) ” 
  &&  “ (j <= (amount_pre + 1 )) ” 
  &&  “ (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l j amount_pre ) ”
  &&  (((( &( "dp" ) ) + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "dp" ) ) j 0 (amount_pre + 1 ) dp_l )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
.

Definition coinChange_partial_solve_wit_6 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (res: Z) (PreH1 : (res > 0)) (PreH2 : (0 <= res)) (PreH3 : (res <= amount_pre)) (PreH4 : (DpReachableTable coins_l dp_l (amount_pre + 1 ) )) (PreH5 : (NoReachableAbove coins_l amount_pre res )) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full ( &( "dp" ) ) (amount_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
|--
  “ (res > 0) ” 
  &&  “ (0 <= res) ” 
  &&  “ (res <= amount_pre) ” 
  &&  “ (DpReachableTable coins_l dp_l (amount_pre + 1 ) ) ” 
  &&  “ (NoReachableAbove coins_l amount_pre res ) ”
  &&  (((( &( "dp" ) ) + (res * sizeof(INT)))) # Int  |-> (Znth res dp_l 0))
  **  (IntArray.missing_i ( &( "dp" ) ) res 0 (amount_pre + 1 ) dp_l )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (amount_pre + 1 ) 100001 )
.

Module Type VC_Correct.


Axiom proof_of_coinChange_safety_wit_1 : coinChange_safety_wit_1.
Axiom proof_of_coinChange_safety_wit_2 : coinChange_safety_wit_2.
Axiom proof_of_coinChange_safety_wit_3 : coinChange_safety_wit_3.
Axiom proof_of_coinChange_safety_wit_4 : coinChange_safety_wit_4.
Axiom proof_of_coinChange_safety_wit_5 : coinChange_safety_wit_5.
Axiom proof_of_coinChange_safety_wit_6 : coinChange_safety_wit_6.
Axiom proof_of_coinChange_safety_wit_7 : coinChange_safety_wit_7.
Axiom proof_of_coinChange_safety_wit_8 : coinChange_safety_wit_8.
Axiom proof_of_coinChange_safety_wit_9 : coinChange_safety_wit_9.
Axiom proof_of_coinChange_safety_wit_10 : coinChange_safety_wit_10.
Axiom proof_of_coinChange_safety_wit_11 : coinChange_safety_wit_11.
Axiom proof_of_coinChange_safety_wit_12 : coinChange_safety_wit_12.
Axiom proof_of_coinChange_safety_wit_13 : coinChange_safety_wit_13.
Axiom proof_of_coinChange_safety_wit_14 : coinChange_safety_wit_14.
Axiom proof_of_coinChange_safety_wit_15 : coinChange_safety_wit_15.
Axiom proof_of_coinChange_safety_wit_16 : coinChange_safety_wit_16.
Axiom proof_of_coinChange_entail_wit_1 : coinChange_entail_wit_1.
Axiom proof_of_coinChange_entail_wit_2 : coinChange_entail_wit_2.
Axiom proof_of_coinChange_entail_wit_3 : coinChange_entail_wit_3.
Axiom proof_of_coinChange_entail_wit_4 : coinChange_entail_wit_4.
Axiom proof_of_coinChange_entail_wit_5_1 : coinChange_entail_wit_5_1.
Axiom proof_of_coinChange_entail_wit_5_2 : coinChange_entail_wit_5_2.
Axiom proof_of_coinChange_entail_wit_6_1 : coinChange_entail_wit_6_1.
Axiom proof_of_coinChange_entail_wit_6_2 : coinChange_entail_wit_6_2.
Axiom proof_of_coinChange_entail_wit_7 : coinChange_entail_wit_7.
Axiom proof_of_coinChange_entail_wit_8 : coinChange_entail_wit_8.
Axiom proof_of_coinChange_entail_wit_9_1 : coinChange_entail_wit_9_1.
Axiom proof_of_coinChange_entail_wit_9_2 : coinChange_entail_wit_9_2.
Axiom proof_of_coinChange_return_wit_1 : coinChange_return_wit_1.
Axiom proof_of_coinChange_partial_solve_wit_1 : coinChange_partial_solve_wit_1.
Axiom proof_of_coinChange_partial_solve_wit_2 : coinChange_partial_solve_wit_2.
Axiom proof_of_coinChange_partial_solve_wit_3 : coinChange_partial_solve_wit_3.
Axiom proof_of_coinChange_partial_solve_wit_4 : coinChange_partial_solve_wit_4.
Axiom proof_of_coinChange_partial_solve_wit_5 : coinChange_partial_solve_wit_5.
Axiom proof_of_coinChange_partial_solve_wit_6 : coinChange_partial_solve_wit_6.

End VC_Correct.
