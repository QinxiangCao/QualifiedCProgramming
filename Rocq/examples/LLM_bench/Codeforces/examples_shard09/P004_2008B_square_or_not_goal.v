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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P004_2008B_square_or_not_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (bits)) = n_pre)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i bits 0) = 48) \/ ((Znth i bits 0) = 49)))) (PreH5 : (Pre bits )) ,
  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (r: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (bits)) = n_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH5 : (Pre bits )) (PreH6 : (0 <= r)) (PreH7 : (r <= 447)) (PreH8 : ((r * r ) <= n_pre)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (((r + 1 ) * (r + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((r + 1 ) * (r + 1 ) )) ”
.

Definition solver_safety_wit_3 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (r: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (bits)) = n_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH5 : (Pre bits )) (PreH6 : (0 <= r)) (PreH7 : (r <= 447)) (PreH8 : ((r * r ) <= n_pre)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ ((r + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition solver_safety_wit_4 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (r: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (bits)) = n_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH5 : (Pre bits )) (PreH6 : (0 <= r)) (PreH7 : (r <= 447)) (PreH8 : ((r * r ) <= n_pre)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ ((r + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition solver_safety_wit_5 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (r: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (bits)) = n_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH5 : (Pre bits )) (PreH6 : (0 <= r)) (PreH7 : (r <= 447)) (PreH8 : ((r * r ) <= n_pre)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (r: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (bits)) = n_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH5 : (Pre bits )) (PreH6 : (0 <= r)) (PreH7 : (r <= 447)) (PreH8 : ((r * r ) <= n_pre)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_7 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (r: Z) (PreH1 : (((r + 1 ) * (r + 1 ) ) <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH6 : (Pre bits )) (PreH7 : (0 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r ) <= n_pre)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ ((r + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition solver_safety_wit_8 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (r: Z) (PreH1 : (((r + 1 ) * (r + 1 ) ) > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH6 : (Pre bits )) (PreH7 : (0 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r ) <= n_pre)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ ((r * r ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r * r )) ”
.

Definition solver_safety_wit_9 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (r: Z) (PreH1 : ((r * r ) <> n_pre)) (PreH2 : (((r + 1 ) * (r + 1 ) ) > n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH7 : (Pre bits )) (PreH8 : (0 <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r ) <= n_pre)) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (r: Z) (PreH1 : ((r * r ) = n_pre)) (PreH2 : (((r + 1 ) * (r + 1 ) ) > n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH7 : (Pre bits )) (PreH8 : (0 <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r ) <= n_pre)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_11 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (i: Z) (r: Z) (PreH1 : (i < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH6 : (Pre bits )) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r ) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= r)) (PreH12 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_12 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH6 : (Pre bits )) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r ) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < r)) (PreH12 : (0 <= j)) (PreH13 : (j <= r)) (PreH14 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH15 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "border" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_13 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (i <> 0)) (PreH2 : (j < r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH7 : (Pre bits )) (PreH8 : (1 <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r ) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < r)) (PreH13 : (0 <= j)) (PreH14 : (j <= r)) (PreH15 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH16 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "border" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ ((r - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r - 1 )) ”
.

Definition solver_safety_wit_14 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (i <> 0)) (PreH2 : (j < r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH7 : (Pre bits )) (PreH8 : (1 <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r ) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < r)) (PreH13 : (0 <= j)) (PreH14 : (j <= r)) (PreH15 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH16 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "border" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_15 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (i <> (r - 1 ))) (PreH2 : (i <> 0)) (PreH3 : (j < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (bits)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH8 : (Pre bits )) (PreH9 : (1 <= r)) (PreH10 : (r <= 447)) (PreH11 : ((r * r ) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < r)) (PreH14 : (0 <= j)) (PreH15 : (j <= r)) (PreH16 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH17 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "border" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_16 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> (r - 1 ))) (PreH3 : (i <> 0)) (PreH4 : (j < r)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (bits)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH9 : (Pre bits )) (PreH10 : (1 <= r)) (PreH11 : (r <= 447)) (PreH12 : ((r * r ) = n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < r)) (PreH15 : (0 <= j)) (PreH16 : (j <= r)) (PreH17 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH18 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "border" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ ((r - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r - 1 )) ”
.

Definition solver_safety_wit_17 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> (r - 1 ))) (PreH3 : (i <> 0)) (PreH4 : (j < r)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (bits)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH9 : (Pre bits )) (PreH10 : (1 <= r)) (PreH11 : (r <= 447)) (PreH12 : ((r * r ) = n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < r)) (PreH15 : (0 <= j)) (PreH16 : (j <= r)) (PreH17 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH18 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "border" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_18 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j = 0)) (PreH2 : (i <> (r - 1 ))) (PreH3 : (i <> 0)) (PreH4 : (j < r)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (bits)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH9 : (Pre bits )) (PreH10 : (1 <= r)) (PreH11 : (r <= 447)) (PreH12 : ((r * r ) = n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < r)) (PreH15 : (0 <= j)) (PreH16 : (j <= r)) (PreH17 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH18 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "want" ) )) # Char  |->_)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (49 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_19 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (i = 0)) (PreH2 : (j < r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH7 : (Pre bits )) (PreH8 : (1 <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r ) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < r)) (PreH13 : (0 <= j)) (PreH14 : (j <= r)) (PreH15 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH16 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "want" ) )) # Char  |->_)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (49 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_20 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (i = (r - 1 ))) (PreH2 : (i <> 0)) (PreH3 : (j < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (bits)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH8 : (Pre bits )) (PreH9 : (1 <= r)) (PreH10 : (r <= 447)) (PreH11 : ((r * r ) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < r)) (PreH14 : (0 <= j)) (PreH15 : (j <= r)) (PreH16 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH17 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "want" ) )) # Char  |->_)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (49 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_21 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j = (r - 1 ))) (PreH2 : (j <> 0)) (PreH3 : (i <> (r - 1 ))) (PreH4 : (i <> 0)) (PreH5 : (j < r)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : ((Zlength (bits)) = n_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH10 : (Pre bits )) (PreH11 : (1 <= r)) (PreH12 : (r <= 447)) (PreH13 : ((r * r ) = n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < r)) (PreH16 : (0 <= j)) (PreH17 : (j <= r)) (PreH18 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH19 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "want" ) )) # Char  |->_)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (49 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_22 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j <> (r - 1 ))) (PreH2 : (j <> 0)) (PreH3 : (i <> (r - 1 ))) (PreH4 : (i <> 0)) (PreH5 : (j < r)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : ((Zlength (bits)) = n_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH10 : (Pre bits )) (PreH11 : (1 <= r)) (PreH12 : (r <= 447)) (PreH13 : ((r * r ) = n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < r)) (PreH16 : (0 <= j)) (PreH17 : (j <= r)) (PreH18 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH19 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "want" ) )) # Char  |->_)
  **  ((( &( "border" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition solver_safety_wit_23 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (0 <= ((i * r ) + j ))) (PreH2 : (((i * r ) + j ) < n_pre)) (PreH3 : (0 <= INT_MAX)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (j <> (r - 1 ))) (PreH6 : (j <> 0)) (PreH7 : (i <> (r - 1 ))) (PreH8 : (i <> 0)) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH14 : (Pre bits )) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r ) = n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < r)) (PreH20 : (0 <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH23 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "want" ) )) # Char  |-> 48)
  **  ((( &( "border" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (((i * r ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * r ) + j )) ”
.

Definition solver_safety_wit_24 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (0 <= ((i * r ) + j ))) (PreH2 : (((i * r ) + j ) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (j = (r - 1 ))) (PreH6 : (j <> 0)) (PreH7 : (i <> (r - 1 ))) (PreH8 : (i <> 0)) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH14 : (Pre bits )) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r ) = n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < r)) (PreH20 : (0 <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH23 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "want" ) )) # Char  |-> 49)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (((i * r ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * r ) + j )) ”
.

Definition solver_safety_wit_25 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (0 <= ((i * r ) + j ))) (PreH2 : (((i * r ) + j ) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (i = (r - 1 ))) (PreH6 : (i <> 0)) (PreH7 : (j < r)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : ((Zlength (bits)) = n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH12 : (Pre bits )) (PreH13 : (1 <= r)) (PreH14 : (r <= 447)) (PreH15 : ((r * r ) = n_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < r)) (PreH18 : (0 <= j)) (PreH19 : (j <= r)) (PreH20 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH21 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "want" ) )) # Char  |-> 49)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (((i * r ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * r ) + j )) ”
.

Definition solver_safety_wit_26 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (0 <= ((i * r ) + j ))) (PreH2 : (((i * r ) + j ) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (i = 0)) (PreH6 : (j < r)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((Zlength (bits)) = n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH11 : (Pre bits )) (PreH12 : (1 <= r)) (PreH13 : (r <= 447)) (PreH14 : ((r * r ) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < r)) (PreH17 : (0 <= j)) (PreH18 : (j <= r)) (PreH19 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH20 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "want" ) )) # Char  |-> 49)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (((i * r ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * r ) + j )) ”
.

Definition solver_safety_wit_27 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (0 <= ((i * r ) + j ))) (PreH2 : (((i * r ) + j ) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (j = 0)) (PreH6 : (i <> (r - 1 ))) (PreH7 : (i <> 0)) (PreH8 : (j < r)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((Zlength (bits)) = n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH13 : (Pre bits )) (PreH14 : (1 <= r)) (PreH15 : (r <= 447)) (PreH16 : ((r * r ) = n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < r)) (PreH19 : (0 <= j)) (PreH20 : (j <= r)) (PreH21 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH22 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "want" ) )) # Char  |-> 49)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (((i * r ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * r ) + j )) ”
.

Definition solver_safety_wit_28 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (0 <= ((i * r ) + j ))) (PreH2 : (((i * r ) + j ) < n_pre)) (PreH3 : (0 <= INT_MAX)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (j <> (r - 1 ))) (PreH6 : (j <> 0)) (PreH7 : (i <> (r - 1 ))) (PreH8 : (i <> 0)) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH14 : (Pre bits )) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r ) = n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < r)) (PreH20 : (0 <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH23 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "want" ) )) # Char  |-> 48)
  **  ((( &( "border" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ ((i * r ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * r )) ”
.

Definition solver_safety_wit_29 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (0 <= ((i * r ) + j ))) (PreH2 : (((i * r ) + j ) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (j = (r - 1 ))) (PreH6 : (j <> 0)) (PreH7 : (i <> (r - 1 ))) (PreH8 : (i <> 0)) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH14 : (Pre bits )) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r ) = n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < r)) (PreH20 : (0 <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH23 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "want" ) )) # Char  |-> 49)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ ((i * r ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * r )) ”
.

Definition solver_safety_wit_30 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (0 <= ((i * r ) + j ))) (PreH2 : (((i * r ) + j ) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (i = (r - 1 ))) (PreH6 : (i <> 0)) (PreH7 : (j < r)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : ((Zlength (bits)) = n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH12 : (Pre bits )) (PreH13 : (1 <= r)) (PreH14 : (r <= 447)) (PreH15 : ((r * r ) = n_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < r)) (PreH18 : (0 <= j)) (PreH19 : (j <= r)) (PreH20 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH21 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "want" ) )) # Char  |-> 49)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ ((i * r ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * r )) ”
.

Definition solver_safety_wit_31 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (0 <= ((i * r ) + j ))) (PreH2 : (((i * r ) + j ) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (i = 0)) (PreH6 : (j < r)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((Zlength (bits)) = n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH11 : (Pre bits )) (PreH12 : (1 <= r)) (PreH13 : (r <= 447)) (PreH14 : ((r * r ) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < r)) (PreH17 : (0 <= j)) (PreH18 : (j <= r)) (PreH19 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH20 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "want" ) )) # Char  |-> 49)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ ((i * r ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * r )) ”
.

Definition solver_safety_wit_32 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (0 <= ((i * r ) + j ))) (PreH2 : (((i * r ) + j ) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (j = 0)) (PreH6 : (i <> (r - 1 ))) (PreH7 : (i <> 0)) (PreH8 : (j < r)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((Zlength (bits)) = n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH13 : (Pre bits )) (PreH14 : (1 <= r)) (PreH15 : (r <= 447)) (PreH16 : ((r * r ) = n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < r)) (PreH19 : (0 <= j)) (PreH20 : (j <= r)) (PreH21 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH22 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "want" ) )) # Char  |-> 49)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ ((i * r ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * r )) ”
.

Definition solver_safety_wit_33 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) <> 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = 0)) (PreH7 : (i <> (r - 1 ))) (PreH8 : (i <> 0)) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH14 : (Pre bits )) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r ) = n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < r)) (PreH20 : (0 <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH23 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "want" ) )) # Char  |-> 49)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_34 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) <> 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = 0)) (PreH7 : (j < r)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : ((Zlength (bits)) = n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH12 : (Pre bits )) (PreH13 : (1 <= r)) (PreH14 : (r <= 447)) (PreH15 : ((r * r ) = n_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < r)) (PreH18 : (0 <= j)) (PreH19 : (j <= r)) (PreH20 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH21 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "want" ) )) # Char  |-> 49)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_35 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) <> 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = (r - 1 ))) (PreH7 : (i <> 0)) (PreH8 : (j < r)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((Zlength (bits)) = n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH13 : (Pre bits )) (PreH14 : (1 <= r)) (PreH15 : (r <= 447)) (PreH16 : ((r * r ) = n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < r)) (PreH19 : (0 <= j)) (PreH20 : (j <= r)) (PreH21 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH22 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "want" ) )) # Char  |-> 49)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_36 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) <> 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = (r - 1 ))) (PreH7 : (j <> 0)) (PreH8 : (i <> (r - 1 ))) (PreH9 : (i <> 0)) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH15 : (Pre bits )) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r ) = n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < r)) (PreH21 : (0 <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH24 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "want" ) )) # Char  |-> 49)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_37 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) <> 48)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (j <> (r - 1 ))) (PreH7 : (j <> 0)) (PreH8 : (i <> (r - 1 ))) (PreH9 : (i <> 0)) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH15 : (Pre bits )) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r ) = n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < r)) (PreH21 : (0 <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH24 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "want" ) )) # Char  |-> 48)
  **  ((( &( "border" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_38 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH6 : (Pre bits )) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r ) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < r)) (PreH12 : (0 <= j)) (PreH13 : (j <= r)) (PreH14 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH15 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_39 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) = 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = 0)) (PreH7 : (i <> (r - 1 ))) (PreH8 : (i <> 0)) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH14 : (Pre bits )) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r ) = n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < r)) (PreH20 : (0 <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH23 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_40 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) = 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = 0)) (PreH7 : (j < r)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : ((Zlength (bits)) = n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH12 : (Pre bits )) (PreH13 : (1 <= r)) (PreH14 : (r <= 447)) (PreH15 : ((r * r ) = n_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < r)) (PreH18 : (0 <= j)) (PreH19 : (j <= r)) (PreH20 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH21 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_41 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) = 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = (r - 1 ))) (PreH7 : (i <> 0)) (PreH8 : (j < r)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((Zlength (bits)) = n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH13 : (Pre bits )) (PreH14 : (1 <= r)) (PreH15 : (r <= 447)) (PreH16 : ((r * r ) = n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < r)) (PreH19 : (0 <= j)) (PreH20 : (j <= r)) (PreH21 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH22 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_42 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) = 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = (r - 1 ))) (PreH7 : (j <> 0)) (PreH8 : (i <> (r - 1 ))) (PreH9 : (i <> 0)) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH15 : (Pre bits )) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r ) = n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < r)) (PreH21 : (0 <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH24 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_43 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) = 48)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (j <> (r - 1 ))) (PreH7 : (j <> 0)) (PreH8 : (i <> (r - 1 ))) (PreH9 : (i <> 0)) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH15 : (Pre bits )) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r ) = n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < r)) (PreH21 : (0 <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH24 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_44 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (i: Z) (r: Z) (PreH1 : (i >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH6 : (Pre bits )) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r ) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= r)) (PreH12 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (bits)) = n_pre)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i bits 0) = 48) \/ ((Znth i bits 0) = 49)))) (PreH5 : (Pre bits )) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (bits)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ” 
  &&  “ (Pre bits ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 447) ” 
  &&  “ ((0 * 0 ) <= n_pre) ”
  &&  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (bits)) = n_pre)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i bits 0) = 48) \/ ((Znth i bits 0) = 49)))) (PreH5 : (Pre bits )) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (bits)) = n_pre)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i bits 0) = 48) \/ ((Znth i bits 0) = 49)))) (PreH5 : (Pre bits )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))
.

Definition solver_entail_wit_2 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (r: Z) (PreH1 : (((r + 1 ) * (r + 1 ) ) <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH6 : (Pre bits )) (PreH7 : (0 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r ) <= n_pre)) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (bits)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ” 
  &&  “ (Pre bits ) ” 
  &&  “ (0 <= (r + 1 )) ” 
  &&  “ ((r + 1 ) <= 447) ” 
  &&  “ (((r + 1 ) * (r + 1 ) ) <= n_pre) ”
  &&  (CharArray.full s_pre n_pre bits )
.

Definition solver_entail_wit_3 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (r: Z) (PreH1 : ((r * r ) = n_pre)) (PreH2 : (((r + 1 ) * (r + 1 ) ) > n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 bits 0) = 48) \/ ((Znth k_2 bits 0) = 49)))) (PreH7 : (Pre bits )) (PreH8 : (0 <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r ) <= n_pre)) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (bits)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ” 
  &&  “ (Pre bits ) ” 
  &&  “ (1 <= r) ” 
  &&  “ (r <= 447) ” 
  &&  “ ((r * r ) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= r) ” 
  &&  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < 0)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ”
  &&  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (r: Z) (PreH1 : ((r * r ) = n_pre)) (PreH2 : (((r + 1 ) * (r + 1 ) ) > n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 bits 0) = 48) \/ ((Znth k_2 bits 0) = 49)))) (PreH7 : (Pre bits )) (PreH8 : (0 <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r ) <= n_pre)) ,
  TT && emp 
|--
  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < 0)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (r: Z) (PreH1 : ((r * r ) = n_pre)) (PreH2 : (((r + 1 ) * (r + 1 ) ) > n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 bits 0) = 48) \/ ((Znth k_2 bits 0) = 49)))) (PreH7 : (Pre bits )) (PreH8 : (0 <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r ) <= n_pre)) ,
  forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < 0)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))
.

Definition solver_entail_wit_3_split_goal_2 := 
forall (n_pre: Z) (bits: (@list Z)) (r: Z) (PreH1 : ((r * r ) = n_pre)) (PreH2 : (((r + 1 ) * (r + 1 ) ) > n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 bits 0) = 48) \/ ((Znth k_2 bits 0) = 49)))) (PreH7 : (Pre bits )) (PreH8 : (0 <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r ) <= n_pre)) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))
.

Definition solver_entail_wit_4 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (i: Z) (r: Z) (PreH1 : (i < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 bits 0) = 48) \/ ((Znth k_2 bits 0) = 49)))) (PreH6 : (Pre bits )) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r ) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= r)) (PreH12 : forall (x_2: Z) , forall (y_3: Z) , (((((0 <= x_2) /\ (x_2 < i)) /\ (0 <= y_3)) /\ (y_3 < r)) -> ((((((x_2 = 0) \/ (x_2 = (r - 1 ))) \/ (y_3 = 0)) \/ (y_3 = (r - 1 ))) /\ ((Znth ((x_2 * r ) + y_3 ) bits 0) = 49)) \/ (((((x_2 <> 0) /\ (x_2 <> (r - 1 ))) /\ (y_3 <> 0)) /\ (y_3 <> (r - 1 ))) /\ ((Znth ((x_2 * r ) + y_3 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (bits)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ” 
  &&  “ (Pre bits ) ” 
  &&  “ (1 <= r) ” 
  &&  “ (r <= 447) ” 
  &&  “ ((r * r ) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= r) ” 
  &&  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ” 
  &&  “ forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < 0)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48)))) ”
  &&  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (i: Z) (r: Z) (PreH1 : (i < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 bits 0) = 48) \/ ((Znth k_2 bits 0) = 49)))) (PreH6 : (Pre bits )) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r ) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= r)) (PreH12 : forall (x_2: Z) , forall (y_3: Z) , (((((0 <= x_2) /\ (x_2 < i)) /\ (0 <= y_3)) /\ (y_3 < r)) -> ((((((x_2 = 0) \/ (x_2 = (r - 1 ))) \/ (y_3 = 0)) \/ (y_3 = (r - 1 ))) /\ ((Znth ((x_2 * r ) + y_3 ) bits 0) = 49)) \/ (((((x_2 <> 0) /\ (x_2 <> (r - 1 ))) /\ (y_3 <> 0)) /\ (y_3 <> (r - 1 ))) /\ ((Znth ((x_2 * r ) + y_3 ) bits 0) = 48))))) ,
  TT && emp 
|--
  “ forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < 0)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48)))) ” 
  &&  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (i: Z) (r: Z) (PreH1 : (i < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 bits 0) = 48) \/ ((Znth k_2 bits 0) = 49)))) (PreH6 : (Pre bits )) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r ) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= r)) (PreH12 : forall (x_2: Z) , forall (y_3: Z) , (((((0 <= x_2) /\ (x_2 < i)) /\ (0 <= y_3)) /\ (y_3 < r)) -> ((((((x_2 = 0) \/ (x_2 = (r - 1 ))) \/ (y_3 = 0)) \/ (y_3 = (r - 1 ))) /\ ((Znth ((x_2 * r ) + y_3 ) bits 0) = 49)) \/ (((((x_2 <> 0) /\ (x_2 <> (r - 1 ))) /\ (y_3 <> 0)) /\ (y_3 <> (r - 1 ))) /\ ((Znth ((x_2 * r ) + y_3 ) bits 0) = 48))))) ,
  forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < 0)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))
.

Definition solver_entail_wit_4_split_goal_2 := 
forall (n_pre: Z) (bits: (@list Z)) (i: Z) (r: Z) (PreH1 : (i < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 bits 0) = 48) \/ ((Znth k_2 bits 0) = 49)))) (PreH6 : (Pre bits )) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r ) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= r)) (PreH12 : forall (x_2: Z) , forall (y_3: Z) , (((((0 <= x_2) /\ (x_2 < i)) /\ (0 <= y_3)) /\ (y_3 < r)) -> ((((((x_2 = 0) \/ (x_2 = (r - 1 ))) \/ (y_3 = 0)) \/ (y_3 = (r - 1 ))) /\ ((Znth ((x_2 * r ) + y_3 ) bits 0) = 49)) \/ (((((x_2 <> 0) /\ (x_2 <> (r - 1 ))) /\ (y_3 <> 0)) /\ (y_3 <> (r - 1 ))) /\ ((Znth ((x_2 * r ) + y_3 ) bits 0) = 48))))) ,
  forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))
.

Definition solver_entail_wit_4_split_goal_3 := 
forall (n_pre: Z) (bits: (@list Z)) (i: Z) (r: Z) (PreH1 : (i < r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 bits 0) = 48) \/ ((Znth k_2 bits 0) = 49)))) (PreH6 : (Pre bits )) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r ) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= r)) (PreH12 : forall (x_2: Z) , forall (y_3: Z) , (((((0 <= x_2) /\ (x_2 < i)) /\ (0 <= y_3)) /\ (y_3 < r)) -> ((((((x_2 = 0) \/ (x_2 = (r - 1 ))) \/ (y_3 = 0)) \/ (y_3 = (r - 1 ))) /\ ((Znth ((x_2 * r ) + y_3 ) bits 0) = 49)) \/ (((((x_2 <> 0) /\ (x_2 <> (r - 1 ))) /\ (y_3 <> 0)) /\ (y_3 <> (r - 1 ))) /\ ((Znth ((x_2 * r ) + y_3 ) bits 0) = 48))))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))
.

Definition solver_entail_wit_5_1 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j = 0)) (PreH2 : (i <> (r - 1 ))) (PreH3 : (i <> 0)) (PreH4 : (j < r)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : ((Zlength (bits)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH9 : (Pre bits )) (PreH10 : (1 <= r)) (PreH11 : (r <= 447)) (PreH12 : ((r * r ) = n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i < r)) (PreH15 : (0 <= j)) (PreH16 : (j <= r)) (PreH17 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH18 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "want" ) )) # Char  |-> 49)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (0 <= ((i * r ) + j )) ” 
  &&  “ (((i * r ) + j ) < n_pre) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ (1 >= INT_MIN) ” 
  &&  “ (j = 0) ” 
  &&  “ (i <> (r - 1 )) ” 
  &&  “ (i <> 0) ” 
  &&  “ (j < r) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (bits)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ” 
  &&  “ (Pre bits ) ” 
  &&  “ (1 <= r) ” 
  &&  “ (r <= 447) ” 
  &&  “ ((r * r ) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= r) ” 
  &&  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ” 
  &&  “ forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48)))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "want" ) )) # Char  |-> 49)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (r <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (1 <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (r >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (1 >= INT_MIN)) (PreH11 : (j = 0)) (PreH12 : (i <> (r - 1 ))) (PreH13 : (i <> 0)) (PreH14 : (j < r)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : ((Zlength (bits)) = n_pre)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH19 : (Pre bits )) (PreH20 : (1 <= r)) (PreH21 : (r <= 447)) (PreH22 : ((r * r ) = n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < r)) (PreH25 : (0 <= j)) (PreH26 : (j <= r)) (PreH27 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH28 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  TT && emp 
|--
  “ (((i * r ) + 0 ) < (r * r )) ”
  &&  emp
).

Definition solver_entail_wit_5_1_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (r <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (1 <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (r >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (1 >= INT_MIN)) (PreH11 : (j = 0)) (PreH12 : (i <> (r - 1 ))) (PreH13 : (i <> 0)) (PreH14 : (j < r)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : ((Zlength (bits)) = n_pre)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH19 : (Pre bits )) (PreH20 : (1 <= r)) (PreH21 : (r <= 447)) (PreH22 : ((r * r ) = n_pre)) (PreH23 : (0 <= i)) (PreH24 : (i < r)) (PreH25 : (0 <= j)) (PreH26 : (j <= r)) (PreH27 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH28 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (((i * r ) + 0 ) < (r * r ))
.

Definition solver_entail_wit_5_2 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (i = 0)) (PreH2 : (j < r)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH7 : (Pre bits )) (PreH8 : (1 <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r ) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < r)) (PreH13 : (0 <= j)) (PreH14 : (j <= r)) (PreH15 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH16 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "want" ) )) # Char  |-> 49)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (0 <= ((i * r ) + j )) ” 
  &&  “ (((i * r ) + j ) < n_pre) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ (1 >= INT_MIN) ” 
  &&  “ (i = 0) ” 
  &&  “ (j < r) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (bits)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ” 
  &&  “ (Pre bits ) ” 
  &&  “ (1 <= r) ” 
  &&  “ (r <= 447) ” 
  &&  “ ((r * r ) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= r) ” 
  &&  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ” 
  &&  “ forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48)))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "want" ) )) # Char  |-> 49)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre n_pre bits )
.

Definition solver_entail_wit_5_3 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (i = (r - 1 ))) (PreH2 : (i <> 0)) (PreH3 : (j < r)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (bits)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH8 : (Pre bits )) (PreH9 : (1 <= r)) (PreH10 : (r <= 447)) (PreH11 : ((r * r ) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i < r)) (PreH14 : (0 <= j)) (PreH15 : (j <= r)) (PreH16 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH17 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "want" ) )) # Char  |-> 49)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (0 <= ((i * r ) + j )) ” 
  &&  “ (((i * r ) + j ) < n_pre) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ (1 >= INT_MIN) ” 
  &&  “ (i = (r - 1 )) ” 
  &&  “ (i <> 0) ” 
  &&  “ (j < r) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (bits)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ” 
  &&  “ (Pre bits ) ” 
  &&  “ (1 <= r) ” 
  &&  “ (r <= 447) ” 
  &&  “ ((r * r ) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= r) ” 
  &&  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ” 
  &&  “ forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48)))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "want" ) )) # Char  |-> 49)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (r <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (1 <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (r >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (1 >= INT_MIN)) (PreH11 : (i = (r - 1 ))) (PreH12 : (i <> 0)) (PreH13 : (j < r)) (PreH14 : (2 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : ((Zlength (bits)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH18 : (Pre bits )) (PreH19 : (1 <= r)) (PreH20 : (r <= 447)) (PreH21 : ((r * r ) = n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i < r)) (PreH24 : (0 <= j)) (PreH25 : (j <= r)) (PreH26 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH27 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  TT && emp 
|--
  “ ((((r - 1 ) * r ) + j ) < (r * r )) ”
  &&  emp
).

Definition solver_entail_wit_5_3_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (r <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (1 <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (r >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (1 >= INT_MIN)) (PreH11 : (i = (r - 1 ))) (PreH12 : (i <> 0)) (PreH13 : (j < r)) (PreH14 : (2 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : ((Zlength (bits)) = n_pre)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH18 : (Pre bits )) (PreH19 : (1 <= r)) (PreH20 : (r <= 447)) (PreH21 : ((r * r ) = n_pre)) (PreH22 : (0 <= i)) (PreH23 : (i < r)) (PreH24 : (0 <= j)) (PreH25 : (j <= r)) (PreH26 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH27 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((((r - 1 ) * r ) + j ) < (r * r ))
.

Definition solver_entail_wit_5_4 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j = (r - 1 ))) (PreH2 : (j <> 0)) (PreH3 : (i <> (r - 1 ))) (PreH4 : (i <> 0)) (PreH5 : (j < r)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : ((Zlength (bits)) = n_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH10 : (Pre bits )) (PreH11 : (1 <= r)) (PreH12 : (r <= 447)) (PreH13 : ((r * r ) = n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < r)) (PreH16 : (0 <= j)) (PreH17 : (j <= r)) (PreH18 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH19 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "want" ) )) # Char  |-> 49)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (0 <= ((i * r ) + j )) ” 
  &&  “ (((i * r ) + j ) < n_pre) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ (1 >= INT_MIN) ” 
  &&  “ (j = (r - 1 )) ” 
  &&  “ (j <> 0) ” 
  &&  “ (i <> (r - 1 )) ” 
  &&  “ (i <> 0) ” 
  &&  “ (j < r) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (bits)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ” 
  &&  “ (Pre bits ) ” 
  &&  “ (1 <= r) ” 
  &&  “ (r <= 447) ” 
  &&  “ ((r * r ) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= r) ” 
  &&  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ” 
  &&  “ forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48)))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "want" ) )) # Char  |-> 49)
  **  ((( &( "border" ) )) # Int  |-> 1)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (r <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (1 <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (r >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (1 >= INT_MIN)) (PreH11 : (j = (r - 1 ))) (PreH12 : (j <> 0)) (PreH13 : (i <> (r - 1 ))) (PreH14 : (i <> 0)) (PreH15 : (j < r)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : ((Zlength (bits)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH20 : (Pre bits )) (PreH21 : (1 <= r)) (PreH22 : (r <= 447)) (PreH23 : ((r * r ) = n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i < r)) (PreH26 : (0 <= j)) (PreH27 : (j <= r)) (PreH28 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH29 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  TT && emp 
|--
  “ (((i * r ) + (r - 1 ) ) < (r * r )) ”
  &&  emp
).

Definition solver_entail_wit_5_4_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (r <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (1 <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (r >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (1 >= INT_MIN)) (PreH11 : (j = (r - 1 ))) (PreH12 : (j <> 0)) (PreH13 : (i <> (r - 1 ))) (PreH14 : (i <> 0)) (PreH15 : (j < r)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : ((Zlength (bits)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH20 : (Pre bits )) (PreH21 : (1 <= r)) (PreH22 : (r <= 447)) (PreH23 : ((r * r ) = n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i < r)) (PreH26 : (0 <= j)) (PreH27 : (j <= r)) (PreH28 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH29 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (((i * r ) + (r - 1 ) ) < (r * r ))
.

Definition solver_entail_wit_5_5 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j <> (r - 1 ))) (PreH2 : (j <> 0)) (PreH3 : (i <> (r - 1 ))) (PreH4 : (i <> 0)) (PreH5 : (j < r)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : ((Zlength (bits)) = n_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH10 : (Pre bits )) (PreH11 : (1 <= r)) (PreH12 : (r <= 447)) (PreH13 : ((r * r ) = n_pre)) (PreH14 : (0 <= i)) (PreH15 : (i < r)) (PreH16 : (0 <= j)) (PreH17 : (j <= r)) (PreH18 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH19 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  ((( &( "want" ) )) # Char  |-> 48)
  **  ((( &( "border" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (0 <= ((i * r ) + j )) ” 
  &&  “ (((i * r ) + j ) < n_pre) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (j <> (r - 1 )) ” 
  &&  “ (j <> 0) ” 
  &&  “ (i <> (r - 1 )) ” 
  &&  “ (i <> 0) ” 
  &&  “ (j < r) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (bits)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ” 
  &&  “ (Pre bits ) ” 
  &&  “ (1 <= r) ” 
  &&  “ (r <= 447) ” 
  &&  “ ((r * r ) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= r) ” 
  &&  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ” 
  &&  “ forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48)))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "want" ) )) # Char  |-> 48)
  **  ((( &( "border" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (r <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (r >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (0 >= INT_MIN)) (PreH11 : (j <> (r - 1 ))) (PreH12 : (j <> 0)) (PreH13 : (i <> (r - 1 ))) (PreH14 : (i <> 0)) (PreH15 : (j < r)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : ((Zlength (bits)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH20 : (Pre bits )) (PreH21 : (1 <= r)) (PreH22 : (r <= 447)) (PreH23 : ((r * r ) = n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i < r)) (PreH26 : (0 <= j)) (PreH27 : (j <= r)) (PreH28 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH29 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  TT && emp 
|--
  “ (((i * r ) + j ) < (r * r )) ”
  &&  emp
).

Definition solver_entail_wit_5_5_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (r <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (0 <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (r >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (0 >= INT_MIN)) (PreH11 : (j <> (r - 1 ))) (PreH12 : (j <> 0)) (PreH13 : (i <> (r - 1 ))) (PreH14 : (i <> 0)) (PreH15 : (j < r)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : ((Zlength (bits)) = n_pre)) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH20 : (Pre bits )) (PreH21 : (1 <= r)) (PreH22 : (r <= 447)) (PreH23 : ((r * r ) = n_pre)) (PreH24 : (0 <= i)) (PreH25 : (i < r)) (PreH26 : (0 <= j)) (PreH27 : (j <= r)) (PreH28 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH29 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (((i * r ) + j ) < (r * r ))
.

Definition solver_entail_wit_6 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 bits 0) = 48) \/ ((Znth k_2 bits 0) = 49)))) (PreH6 : (Pre bits )) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r ) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < r)) (PreH12 : (0 <= j)) (PreH13 : (j <= r)) (PreH14 : forall (x_2: Z) , forall (y_2: Z) , (((((0 <= x_2) /\ (x_2 < i)) /\ (0 <= y_2)) /\ (y_2 < r)) -> ((((((x_2 = 0) \/ (x_2 = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((x_2 * r ) + y_2 ) bits 0) = 49)) \/ (((((x_2 <> 0) /\ (x_2 <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((x_2 * r ) + y_2 ) bits 0) = 48))))) (PreH15 : forall (y_3: Z) , (((0 <= y_3) /\ (y_3 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_3 = 0)) \/ (y_3 = (r - 1 ))) /\ ((Znth ((i * r ) + y_3 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_3 <> 0)) /\ (y_3 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_3 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (bits)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ” 
  &&  “ (Pre bits ) ” 
  &&  “ (1 <= r) ” 
  &&  “ (r <= 447) ” 
  &&  “ ((r * r ) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= r) ” 
  &&  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < (i + 1 ))) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ”
  &&  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 bits 0) = 48) \/ ((Znth k_2 bits 0) = 49)))) (PreH6 : (Pre bits )) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r ) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < r)) (PreH12 : (0 <= j)) (PreH13 : (j <= r)) (PreH14 : forall (x_2: Z) , forall (y_2: Z) , (((((0 <= x_2) /\ (x_2 < i)) /\ (0 <= y_2)) /\ (y_2 < r)) -> ((((((x_2 = 0) \/ (x_2 = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((x_2 * r ) + y_2 ) bits 0) = 49)) \/ (((((x_2 <> 0) /\ (x_2 <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((x_2 * r ) + y_2 ) bits 0) = 48))))) (PreH15 : forall (y_3: Z) , (((0 <= y_3) /\ (y_3 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_3 = 0)) \/ (y_3 = (r - 1 ))) /\ ((Znth ((i * r ) + y_3 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_3 <> 0)) /\ (y_3 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_3 ) bits 0) = 48))))) ,
  TT && emp 
|--
  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < (i + 1 ))) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 bits 0) = 48) \/ ((Znth k_2 bits 0) = 49)))) (PreH6 : (Pre bits )) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r ) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < r)) (PreH12 : (0 <= j)) (PreH13 : (j <= r)) (PreH14 : forall (x_2: Z) , forall (y_2: Z) , (((((0 <= x_2) /\ (x_2 < i)) /\ (0 <= y_2)) /\ (y_2 < r)) -> ((((((x_2 = 0) \/ (x_2 = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((x_2 * r ) + y_2 ) bits 0) = 49)) \/ (((((x_2 <> 0) /\ (x_2 <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((x_2 * r ) + y_2 ) bits 0) = 48))))) (PreH15 : forall (y_3: Z) , (((0 <= y_3) /\ (y_3 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_3 = 0)) \/ (y_3 = (r - 1 ))) /\ ((Znth ((i * r ) + y_3 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_3 <> 0)) /\ (y_3 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_3 ) bits 0) = 48))))) ,
  forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < (i + 1 ))) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))
.

Definition solver_entail_wit_6_split_goal_2 := 
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (j >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> (((Znth k_2 bits 0) = 48) \/ ((Znth k_2 bits 0) = 49)))) (PreH6 : (Pre bits )) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r ) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < r)) (PreH12 : (0 <= j)) (PreH13 : (j <= r)) (PreH14 : forall (x_2: Z) , forall (y_2: Z) , (((((0 <= x_2) /\ (x_2 < i)) /\ (0 <= y_2)) /\ (y_2 < r)) -> ((((((x_2 = 0) \/ (x_2 = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((x_2 * r ) + y_2 ) bits 0) = 49)) \/ (((((x_2 <> 0) /\ (x_2 <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((x_2 * r ) + y_2 ) bits 0) = 48))))) (PreH15 : forall (y_3: Z) , (((0 <= y_3) /\ (y_3 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_3 = 0)) \/ (y_3 = (r - 1 ))) /\ ((Znth ((i * r ) + y_3 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_3 <> 0)) /\ (y_3 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_3 ) bits 0) = 48))))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))
.

Definition solver_entail_wit_7_1 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) = 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = 0)) (PreH7 : (i <> (r - 1 ))) (PreH8 : (i <> 0)) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH14 : (Pre bits )) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r ) = n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < r)) (PreH20 : (0 <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH23 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (bits)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ” 
  &&  “ (Pre bits ) ” 
  &&  “ (1 <= r) ” 
  &&  “ (r <= 447) ” 
  &&  “ ((r * r ) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= r) ” 
  &&  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ” 
  &&  “ forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < (j + 1 ))) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48)))) ”
  &&  (CharArray.full s_pre n_pre bits )
.

Definition solver_entail_wit_7_2 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) = 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = 0)) (PreH7 : (j < r)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : ((Zlength (bits)) = n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH12 : (Pre bits )) (PreH13 : (1 <= r)) (PreH14 : (r <= 447)) (PreH15 : ((r * r ) = n_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < r)) (PreH18 : (0 <= j)) (PreH19 : (j <= r)) (PreH20 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH21 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (bits)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ” 
  &&  “ (Pre bits ) ” 
  &&  “ (1 <= r) ” 
  &&  “ (r <= 447) ” 
  &&  “ ((r * r ) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= r) ” 
  &&  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ” 
  &&  “ forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < (j + 1 ))) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48)))) ”
  &&  (CharArray.full s_pre n_pre bits )
.

Definition solver_entail_wit_7_3 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) = 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = (r - 1 ))) (PreH7 : (i <> 0)) (PreH8 : (j < r)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((Zlength (bits)) = n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH13 : (Pre bits )) (PreH14 : (1 <= r)) (PreH15 : (r <= 447)) (PreH16 : ((r * r ) = n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < r)) (PreH19 : (0 <= j)) (PreH20 : (j <= r)) (PreH21 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH22 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (bits)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ” 
  &&  “ (Pre bits ) ” 
  &&  “ (1 <= r) ” 
  &&  “ (r <= 447) ” 
  &&  “ ((r * r ) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= r) ” 
  &&  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ” 
  &&  “ forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < (j + 1 ))) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48)))) ”
  &&  (CharArray.full s_pre n_pre bits )
.

Definition solver_entail_wit_7_4 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) = 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = (r - 1 ))) (PreH7 : (j <> 0)) (PreH8 : (i <> (r - 1 ))) (PreH9 : (i <> 0)) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH15 : (Pre bits )) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r ) = n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < r)) (PreH21 : (0 <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH24 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (bits)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ” 
  &&  “ (Pre bits ) ” 
  &&  “ (1 <= r) ” 
  &&  “ (r <= 447) ” 
  &&  “ ((r * r ) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= r) ” 
  &&  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ” 
  &&  “ forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < (j + 1 ))) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48)))) ”
  &&  (CharArray.full s_pre n_pre bits )
.

Definition solver_entail_wit_7_5 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) = 48)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (j <> (r - 1 ))) (PreH7 : (j <> 0)) (PreH8 : (i <> (r - 1 ))) (PreH9 : (i <> 0)) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH15 : (Pre bits )) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r ) = n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < r)) (PreH21 : (0 <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH24 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (bits)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ” 
  &&  “ (Pre bits ) ” 
  &&  “ (1 <= r) ” 
  &&  “ (r <= 447) ” 
  &&  “ ((r * r ) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= r) ” 
  &&  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ” 
  &&  “ forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < (j + 1 ))) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48)))) ”
  &&  (CharArray.full s_pre n_pre bits )
.

Definition solver_return_wit_1 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (i: Z) (r: Z) (PreH1 : (i >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH6 : (Pre bits )) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r ) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= r)) (PreH12 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (Spec bits 1 ) ”
  &&  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (i: Z) (r: Z) (PreH1 : (i >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH6 : (Pre bits )) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r ) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= r)) (PreH12 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) ,
  TT && emp 
|--
  “ (Spec bits 1 ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (i: Z) (r: Z) (PreH1 : (i >= r)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (bits)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH6 : (Pre bits )) (PreH7 : (1 <= r)) (PreH8 : (r <= 447)) (PreH9 : ((r * r ) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= r)) (PreH12 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) ,
  (Spec bits 1 )
.

Definition solver_return_wit_2 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) <> 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = 0)) (PreH7 : (i <> (r - 1 ))) (PreH8 : (i <> 0)) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH14 : (Pre bits )) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r ) = n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < r)) (PreH20 : (0 <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH23 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (Spec bits 0 ) ”
  &&  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) <> 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = 0)) (PreH7 : (i <> (r - 1 ))) (PreH8 : (i <> 0)) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH14 : (Pre bits )) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r ) = n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < r)) (PreH20 : (0 <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH23 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  TT && emp 
|--
  “ (Spec bits 0 ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) <> 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = 0)) (PreH7 : (i <> (r - 1 ))) (PreH8 : (i <> 0)) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH14 : (Pre bits )) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r ) = n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < r)) (PreH20 : (0 <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH23 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (Spec bits 0 )
.

Definition solver_return_wit_3 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) <> 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = 0)) (PreH7 : (j < r)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : ((Zlength (bits)) = n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH12 : (Pre bits )) (PreH13 : (1 <= r)) (PreH14 : (r <= 447)) (PreH15 : ((r * r ) = n_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < r)) (PreH18 : (0 <= j)) (PreH19 : (j <= r)) (PreH20 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH21 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (Spec bits 0 ) ”
  &&  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) <> 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = 0)) (PreH7 : (j < r)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : ((Zlength (bits)) = n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH12 : (Pre bits )) (PreH13 : (1 <= r)) (PreH14 : (r <= 447)) (PreH15 : ((r * r ) = n_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < r)) (PreH18 : (0 <= j)) (PreH19 : (j <= r)) (PreH20 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH21 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  TT && emp 
|--
  “ (Spec bits 0 ) ”
  &&  emp
).

Definition solver_return_wit_3_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) <> 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = 0)) (PreH7 : (j < r)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : ((Zlength (bits)) = n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH12 : (Pre bits )) (PreH13 : (1 <= r)) (PreH14 : (r <= 447)) (PreH15 : ((r * r ) = n_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < r)) (PreH18 : (0 <= j)) (PreH19 : (j <= r)) (PreH20 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH21 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (Spec bits 0 )
.

Definition solver_return_wit_4 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) <> 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = (r - 1 ))) (PreH7 : (i <> 0)) (PreH8 : (j < r)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((Zlength (bits)) = n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH13 : (Pre bits )) (PreH14 : (1 <= r)) (PreH15 : (r <= 447)) (PreH16 : ((r * r ) = n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < r)) (PreH19 : (0 <= j)) (PreH20 : (j <= r)) (PreH21 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH22 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (Spec bits 0 ) ”
  &&  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) <> 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = (r - 1 ))) (PreH7 : (i <> 0)) (PreH8 : (j < r)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((Zlength (bits)) = n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH13 : (Pre bits )) (PreH14 : (1 <= r)) (PreH15 : (r <= 447)) (PreH16 : ((r * r ) = n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < r)) (PreH19 : (0 <= j)) (PreH20 : (j <= r)) (PreH21 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH22 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  TT && emp 
|--
  “ (Spec bits 0 ) ”
  &&  emp
).

Definition solver_return_wit_4_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) <> 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (i = (r - 1 ))) (PreH7 : (i <> 0)) (PreH8 : (j < r)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((Zlength (bits)) = n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH13 : (Pre bits )) (PreH14 : (1 <= r)) (PreH15 : (r <= 447)) (PreH16 : ((r * r ) = n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < r)) (PreH19 : (0 <= j)) (PreH20 : (j <= r)) (PreH21 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH22 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (Spec bits 0 )
.

Definition solver_return_wit_5 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) <> 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = (r - 1 ))) (PreH7 : (j <> 0)) (PreH8 : (i <> (r - 1 ))) (PreH9 : (i <> 0)) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH15 : (Pre bits )) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r ) = n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < r)) (PreH21 : (0 <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH24 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (Spec bits 0 ) ”
  &&  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) <> 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = (r - 1 ))) (PreH7 : (j <> 0)) (PreH8 : (i <> (r - 1 ))) (PreH9 : (i <> 0)) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH15 : (Pre bits )) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r ) = n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < r)) (PreH21 : (0 <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH24 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  TT && emp 
|--
  “ (Spec bits 0 ) ”
  &&  emp
).

Definition solver_return_wit_5_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) <> 49)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (1 <= INT_MAX)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (j = (r - 1 ))) (PreH7 : (j <> 0)) (PreH8 : (i <> (r - 1 ))) (PreH9 : (i <> 0)) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH15 : (Pre bits )) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r ) = n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < r)) (PreH21 : (0 <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH24 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (Spec bits 0 )
.

Definition solver_return_wit_6 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) <> 48)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (j <> (r - 1 ))) (PreH7 : (j <> 0)) (PreH8 : (i <> (r - 1 ))) (PreH9 : (i <> 0)) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH15 : (Pre bits )) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r ) = n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < r)) (PreH21 : (0 <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH24 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (Spec bits 0 ) ”
  &&  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) <> 48)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (j <> (r - 1 ))) (PreH7 : (j <> 0)) (PreH8 : (i <> (r - 1 ))) (PreH9 : (i <> 0)) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH15 : (Pre bits )) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r ) = n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < r)) (PreH21 : (0 <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH24 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  TT && emp 
|--
  “ (Spec bits 0 ) ”
  &&  emp
).

Definition solver_return_wit_6_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : ((Znth ((i * r ) + j ) bits 0) <> 48)) (PreH2 : (0 <= ((i * r ) + j ))) (PreH3 : (((i * r ) + j ) < n_pre)) (PreH4 : (0 <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (j <> (r - 1 ))) (PreH7 : (j <> 0)) (PreH8 : (i <> (r - 1 ))) (PreH9 : (i <> 0)) (PreH10 : (j < r)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (bits)) = n_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH15 : (Pre bits )) (PreH16 : (1 <= r)) (PreH17 : (r <= 447)) (PreH18 : ((r * r ) = n_pre)) (PreH19 : (0 <= i)) (PreH20 : (i < r)) (PreH21 : (0 <= j)) (PreH22 : (j <= r)) (PreH23 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH24 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (Spec bits 0 )
.

Definition solver_return_wit_7 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (r: Z) (PreH1 : ((r * r ) <> n_pre)) (PreH2 : (((r + 1 ) * (r + 1 ) ) > n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH7 : (Pre bits )) (PreH8 : (0 <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r ) <= n_pre)) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (Spec bits 0 ) ”
  &&  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (r: Z) (PreH1 : ((r * r ) <> n_pre)) (PreH2 : (((r + 1 ) * (r + 1 ) ) > n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH7 : (Pre bits )) (PreH8 : (0 <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r ) <= n_pre)) ,
  TT && emp 
|--
  “ (Spec bits 0 ) ”
  &&  emp
).

Definition solver_return_wit_7_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (r: Z) (PreH1 : ((r * r ) <> n_pre)) (PreH2 : (((r + 1 ) * (r + 1 ) ) > n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (bits)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH7 : (Pre bits )) (PreH8 : (0 <= r)) (PreH9 : (r <= 447)) (PreH10 : ((r * r ) <= n_pre)) ,
  (Spec bits 0 )
.

Definition solver_partial_solve_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (0 <= ((i * r ) + j ))) (PreH2 : (((i * r ) + j ) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (j = 0)) (PreH6 : (i <> (r - 1 ))) (PreH7 : (i <> 0)) (PreH8 : (j < r)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : ((Zlength (bits)) = n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH13 : (Pre bits )) (PreH14 : (1 <= r)) (PreH15 : (r <= 447)) (PreH16 : ((r * r ) = n_pre)) (PreH17 : (0 <= i)) (PreH18 : (i < r)) (PreH19 : (0 <= j)) (PreH20 : (j <= r)) (PreH21 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH22 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (0 <= ((i * r ) + j )) ” 
  &&  “ (((i * r ) + j ) < n_pre) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ (1 >= INT_MIN) ” 
  &&  “ (j = 0) ” 
  &&  “ (i <> (r - 1 )) ” 
  &&  “ (i <> 0) ” 
  &&  “ (j < r) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (bits)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ” 
  &&  “ (Pre bits ) ” 
  &&  “ (1 <= r) ” 
  &&  “ (r <= 447) ” 
  &&  “ ((r * r ) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= r) ” 
  &&  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ” 
  &&  “ forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48)))) ”
  &&  (((s_pre + (((i * r ) + j ) * sizeof(CHAR)))) # Char  |-> (Znth ((i * r ) + j ) bits 0))
  **  (CharArray.missing_i s_pre ((i * r ) + j ) 0 n_pre bits )
.

Definition solver_partial_solve_wit_2 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (0 <= ((i * r ) + j ))) (PreH2 : (((i * r ) + j ) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (i = 0)) (PreH6 : (j < r)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : ((Zlength (bits)) = n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH11 : (Pre bits )) (PreH12 : (1 <= r)) (PreH13 : (r <= 447)) (PreH14 : ((r * r ) = n_pre)) (PreH15 : (0 <= i)) (PreH16 : (i < r)) (PreH17 : (0 <= j)) (PreH18 : (j <= r)) (PreH19 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH20 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (0 <= ((i * r ) + j )) ” 
  &&  “ (((i * r ) + j ) < n_pre) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ (1 >= INT_MIN) ” 
  &&  “ (i = 0) ” 
  &&  “ (j < r) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (bits)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ” 
  &&  “ (Pre bits ) ” 
  &&  “ (1 <= r) ” 
  &&  “ (r <= 447) ” 
  &&  “ ((r * r ) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= r) ” 
  &&  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ” 
  &&  “ forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48)))) ”
  &&  (((s_pre + (((i * r ) + j ) * sizeof(CHAR)))) # Char  |-> (Znth ((i * r ) + j ) bits 0))
  **  (CharArray.missing_i s_pre ((i * r ) + j ) 0 n_pre bits )
.

Definition solver_partial_solve_wit_3 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (0 <= ((i * r ) + j ))) (PreH2 : (((i * r ) + j ) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (i = (r - 1 ))) (PreH6 : (i <> 0)) (PreH7 : (j < r)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 200000)) (PreH10 : ((Zlength (bits)) = n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH12 : (Pre bits )) (PreH13 : (1 <= r)) (PreH14 : (r <= 447)) (PreH15 : ((r * r ) = n_pre)) (PreH16 : (0 <= i)) (PreH17 : (i < r)) (PreH18 : (0 <= j)) (PreH19 : (j <= r)) (PreH20 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH21 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (0 <= ((i * r ) + j )) ” 
  &&  “ (((i * r ) + j ) < n_pre) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ (1 >= INT_MIN) ” 
  &&  “ (i = (r - 1 )) ” 
  &&  “ (i <> 0) ” 
  &&  “ (j < r) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (bits)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ” 
  &&  “ (Pre bits ) ” 
  &&  “ (1 <= r) ” 
  &&  “ (r <= 447) ” 
  &&  “ ((r * r ) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= r) ” 
  &&  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ” 
  &&  “ forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48)))) ”
  &&  (((s_pre + (((i * r ) + j ) * sizeof(CHAR)))) # Char  |-> (Znth ((i * r ) + j ) bits 0))
  **  (CharArray.missing_i s_pre ((i * r ) + j ) 0 n_pre bits )
.

Definition solver_partial_solve_wit_4 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (0 <= ((i * r ) + j ))) (PreH2 : (((i * r ) + j ) < n_pre)) (PreH3 : (1 <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (j = (r - 1 ))) (PreH6 : (j <> 0)) (PreH7 : (i <> (r - 1 ))) (PreH8 : (i <> 0)) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH14 : (Pre bits )) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r ) = n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < r)) (PreH20 : (0 <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH23 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (0 <= ((i * r ) + j )) ” 
  &&  “ (((i * r ) + j ) < n_pre) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ (1 >= INT_MIN) ” 
  &&  “ (j = (r - 1 )) ” 
  &&  “ (j <> 0) ” 
  &&  “ (i <> (r - 1 )) ” 
  &&  “ (i <> 0) ” 
  &&  “ (j < r) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (bits)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ” 
  &&  “ (Pre bits ) ” 
  &&  “ (1 <= r) ” 
  &&  “ (r <= 447) ” 
  &&  “ ((r * r ) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= r) ” 
  &&  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ” 
  &&  “ forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48)))) ”
  &&  (((s_pre + (((i * r ) + j ) * sizeof(CHAR)))) # Char  |-> (Znth ((i * r ) + j ) bits 0))
  **  (CharArray.missing_i s_pre ((i * r ) + j ) 0 n_pre bits )
.

Definition solver_partial_solve_wit_5 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (j: Z) (i: Z) (r: Z) (PreH1 : (0 <= ((i * r ) + j ))) (PreH2 : (((i * r ) + j ) < n_pre)) (PreH3 : (0 <= INT_MAX)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (j <> (r - 1 ))) (PreH6 : (j <> 0)) (PreH7 : (i <> (r - 1 ))) (PreH8 : (i <> 0)) (PreH9 : (j < r)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (bits)) = n_pre)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49)))) (PreH14 : (Pre bits )) (PreH15 : (1 <= r)) (PreH16 : (r <= 447)) (PreH17 : ((r * r ) = n_pre)) (PreH18 : (0 <= i)) (PreH19 : (i < r)) (PreH20 : (0 <= j)) (PreH21 : (j <= r)) (PreH22 : forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48))))) (PreH23 : forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48))))) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (0 <= ((i * r ) + j )) ” 
  &&  “ (((i * r ) + j ) < n_pre) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (j <> (r - 1 )) ” 
  &&  “ (j <> 0) ” 
  &&  “ (i <> (r - 1 )) ” 
  &&  “ (i <> 0) ” 
  &&  “ (j < r) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (bits)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> (((Znth k bits 0) = 48) \/ ((Znth k bits 0) = 49))) ” 
  &&  “ (Pre bits ) ” 
  &&  “ (1 <= r) ” 
  &&  “ (r <= 447) ” 
  &&  “ ((r * r ) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < r) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= r) ” 
  &&  “ forall (x: Z) , forall (y: Z) , (((((0 <= x) /\ (x < i)) /\ (0 <= y)) /\ (y < r)) -> ((((((x = 0) \/ (x = (r - 1 ))) \/ (y = 0)) \/ (y = (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 49)) \/ (((((x <> 0) /\ (x <> (r - 1 ))) /\ (y <> 0)) /\ (y <> (r - 1 ))) /\ ((Znth ((x * r ) + y ) bits 0) = 48)))) ” 
  &&  “ forall (y_2: Z) , (((0 <= y_2) /\ (y_2 < j)) -> ((((((i = 0) \/ (i = (r - 1 ))) \/ (y_2 = 0)) \/ (y_2 = (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 49)) \/ (((((i <> 0) /\ (i <> (r - 1 ))) /\ (y_2 <> 0)) /\ (y_2 <> (r - 1 ))) /\ ((Znth ((i * r ) + y_2 ) bits 0) = 48)))) ”
  &&  (((s_pre + (((i * r ) + j ) * sizeof(CHAR)))) # Char  |-> (Znth ((i * r ) + j ) bits 0))
  **  (CharArray.missing_i s_pre ((i * r ) + j ) 0 n_pre bits )
.

Module Type VC_Correct.


Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Axiom proof_of_solver_safety_wit_8 : solver_safety_wit_8.
Axiom proof_of_solver_safety_wit_9 : solver_safety_wit_9.
Axiom proof_of_solver_safety_wit_10 : solver_safety_wit_10.
Axiom proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Axiom proof_of_solver_safety_wit_12 : solver_safety_wit_12.
Axiom proof_of_solver_safety_wit_13 : solver_safety_wit_13.
Axiom proof_of_solver_safety_wit_14 : solver_safety_wit_14.
Axiom proof_of_solver_safety_wit_15 : solver_safety_wit_15.
Axiom proof_of_solver_safety_wit_16 : solver_safety_wit_16.
Axiom proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Axiom proof_of_solver_safety_wit_18 : solver_safety_wit_18.
Axiom proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Axiom proof_of_solver_safety_wit_20 : solver_safety_wit_20.
Axiom proof_of_solver_safety_wit_21 : solver_safety_wit_21.
Axiom proof_of_solver_safety_wit_22 : solver_safety_wit_22.
Axiom proof_of_solver_safety_wit_23 : solver_safety_wit_23.
Axiom proof_of_solver_safety_wit_24 : solver_safety_wit_24.
Axiom proof_of_solver_safety_wit_25 : solver_safety_wit_25.
Axiom proof_of_solver_safety_wit_26 : solver_safety_wit_26.
Axiom proof_of_solver_safety_wit_27 : solver_safety_wit_27.
Axiom proof_of_solver_safety_wit_28 : solver_safety_wit_28.
Axiom proof_of_solver_safety_wit_29 : solver_safety_wit_29.
Axiom proof_of_solver_safety_wit_30 : solver_safety_wit_30.
Axiom proof_of_solver_safety_wit_31 : solver_safety_wit_31.
Axiom proof_of_solver_safety_wit_32 : solver_safety_wit_32.
Axiom proof_of_solver_safety_wit_33 : solver_safety_wit_33.
Axiom proof_of_solver_safety_wit_34 : solver_safety_wit_34.
Axiom proof_of_solver_safety_wit_35 : solver_safety_wit_35.
Axiom proof_of_solver_safety_wit_36 : solver_safety_wit_36.
Axiom proof_of_solver_safety_wit_37 : solver_safety_wit_37.
Axiom proof_of_solver_safety_wit_38 : solver_safety_wit_38.
Axiom proof_of_solver_safety_wit_39 : solver_safety_wit_39.
Axiom proof_of_solver_safety_wit_40 : solver_safety_wit_40.
Axiom proof_of_solver_safety_wit_41 : solver_safety_wit_41.
Axiom proof_of_solver_safety_wit_42 : solver_safety_wit_42.
Axiom proof_of_solver_safety_wit_43 : solver_safety_wit_43.
Axiom proof_of_solver_safety_wit_44 : solver_safety_wit_44.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_5_3 : solver_entail_wit_5_3.
Axiom proof_of_solver_entail_wit_5_4 : solver_entail_wit_5_4.
Axiom proof_of_solver_entail_wit_5_5 : solver_entail_wit_5_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Axiom proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Axiom proof_of_solver_entail_wit_7_3 : solver_entail_wit_7_3.
Axiom proof_of_solver_entail_wit_7_4 : solver_entail_wit_7_4.
Axiom proof_of_solver_entail_wit_7_5 : solver_entail_wit_7_5.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_return_wit_4 : solver_return_wit_4.
Axiom proof_of_solver_return_wit_5 : solver_return_wit_5.
Axiom proof_of_solver_return_wit_6 : solver_return_wit_6.
Axiom proof_of_solver_return_wit_7 : solver_return_wit_7.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.

End VC_Correct.
