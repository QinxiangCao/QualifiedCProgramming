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
Require Import SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem.chinese_remainder_theorem_lib.
Local Open Scope sac.

(*----- Function chinese_remainder_theorem -----*)

Definition chinese_remainder_theorem_safety_wit_1 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (PreH1 : (n_pre = (Zlength (moduli_l)))) (PreH2 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH3 : (1 <= (Zlength (moduli_l)))) (PreH4 : (Forall (Z.le (1)) moduli_l )) (PreH5 : (Forall (Z.le (0)) remainders_l )) (PreH6 : (Forall2 Z.lt remainders_l moduli_l )) (PreH7 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH8 : (1 <= (CRTProduct (moduli_l)))) (PreH9 : ((CRTProduct (moduli_l)) <= 46340)) ,
  ((( &( "product" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  (IntArray.full remainders_pre n_pre remainders_l )
  **  (IntArray.full moduli_pre n_pre moduli_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition chinese_remainder_theorem_safety_wit_2 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (PreH1 : (n_pre = (Zlength (moduli_l)))) (PreH2 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH3 : (1 <= (Zlength (moduli_l)))) (PreH4 : (Forall (Z.le (1)) moduli_l )) (PreH5 : (Forall (Z.le (0)) remainders_l )) (PreH6 : (Forall2 Z.lt remainders_l moduli_l )) (PreH7 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH8 : (1 <= (CRTProduct (moduli_l)))) (PreH9 : ((CRTProduct (moduli_l)) <= 46340)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "product" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  (IntArray.full remainders_pre n_pre remainders_l )
  **  (IntArray.full moduli_pre n_pre moduli_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition chinese_remainder_theorem_safety_wit_3 := 
(
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (product: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (product = (CRTProduct ((sublist (0) (i) (moduli_l)))))) (PreH14 : (1 <= product)) (PreH15 : (product <= (CRTProduct (moduli_l)))) ,
  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  (IntArray.full remainders_pre n_pre remainders_l )
|--
  “ ((product * (Znth i moduli_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (product * (Znth i moduli_l 0) )) ”
) \/
(
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (product: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (product = (CRTProduct ((sublist (0) (i) (moduli_l)))))) (PreH14 : (1 <= product)) (PreH15 : (product <= (CRTProduct (moduli_l)))) ,
  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  (IntArray.full remainders_pre n_pre remainders_l )
|--
  “ ((product * (Znth i moduli_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (product * (Znth i moduli_l 0) )) ”
).

Definition chinese_remainder_theorem_safety_wit_3_split_goal_1 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (product: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (product = (CRTProduct ((sublist (0) (i) (moduli_l)))))) (PreH14 : (1 <= product)) (PreH15 : (product <= (CRTProduct (moduli_l)))) ,
  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  (IntArray.full remainders_pre n_pre remainders_l )
|--
  “ ((product * (Znth i moduli_l 0) ) <= INT_MAX) ”
.

Definition chinese_remainder_theorem_safety_wit_3_split_goal_2 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (product: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (product = (CRTProduct ((sublist (0) (i) (moduli_l)))))) (PreH14 : (1 <= product)) (PreH15 : (product <= (CRTProduct (moduli_l)))) ,
  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  (IntArray.full remainders_pre n_pre remainders_l )
|--
  “ ((INT_MIN) <= (product * (Znth i moduli_l 0) )) ”
.

Definition chinese_remainder_theorem_safety_wit_4 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (product: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (product = (CRTProduct ((sublist (0) (i) (moduli_l)))))) (PreH14 : (1 <= product)) (PreH15 : (product <= (CRTProduct (moduli_l)))) ,
  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "product" ) )) # Int  |-> (product * (Znth i moduli_l 0) ))
  **  (IntArray.full remainders_pre n_pre remainders_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition chinese_remainder_theorem_safety_wit_5 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (product: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (product = (CRTProduct ((sublist (0) (i) (moduli_l)))))) (PreH14 : (1 <= product)) (PreH15 : (product <= (CRTProduct (moduli_l)))) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  (IntArray.full remainders_pre n_pre remainders_l )
  **  (IntArray.full moduli_pre n_pre moduli_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition chinese_remainder_theorem_safety_wit_6 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (product: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (product = (CRTProduct ((sublist (0) (i) (moduli_l)))))) (PreH14 : (1 <= product)) (PreH15 : (product <= (CRTProduct (moduli_l)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "result" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  (IntArray.full remainders_pre n_pre remainders_l )
  **  (IntArray.full moduli_pre n_pre moduli_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition chinese_remainder_theorem_safety_wit_7 := 
(
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (product = (CRTProduct (moduli_l)))) (PreH12 : (1 <= product)) (PreH13 : (product <= 46340)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= result)) (PreH17 : (result < product)) (PreH18 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH19 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "partial_product" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  (IntArray.full remainders_pre n_pre remainders_l )
|--
  “ ((product <> (INT_MIN)) \/ ((Znth i moduli_l 0) <> (-1))) ” 
  &&  “ ((Znth i moduli_l 0) <> 0) ”
) \/
(
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (product = (CRTProduct (moduli_l)))) (PreH12 : (1 <= product)) (PreH13 : (product <= 46340)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= result)) (PreH17 : (result < product)) (PreH18 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH19 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "partial_product" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  (IntArray.full remainders_pre n_pre remainders_l )
|--
  “ ((product <> (INT_MIN)) \/ ((Znth i moduli_l 0) <> (-1))) ” 
  &&  “ ((Znth i moduli_l 0) <> 0) ”
).

Definition chinese_remainder_theorem_safety_wit_7_split_goal_1 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (product = (CRTProduct (moduli_l)))) (PreH12 : (1 <= product)) (PreH13 : (product <= 46340)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= result)) (PreH17 : (result < product)) (PreH18 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH19 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "partial_product" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  (IntArray.full remainders_pre n_pre remainders_l )
|--
  “ ((product <> (INT_MIN)) \/ ((Znth i moduli_l 0) <> (-1))) ”
.

Definition chinese_remainder_theorem_safety_wit_7_split_goal_2 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (product = (CRTProduct (moduli_l)))) (PreH12 : (1 <= product)) (PreH13 : (product <= 46340)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= result)) (PreH17 : (result < product)) (PreH18 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH19 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "partial_product" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  (IntArray.full remainders_pre n_pre remainders_l )
|--
  “ ((Znth i moduli_l 0) <> 0) ”
.

Definition chinese_remainder_theorem_safety_wit_8 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH2 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH6 : (1 <= (Zlength (moduli_l)))) (PreH7 : (Forall (Z.le (1)) moduli_l )) (PreH8 : (Forall (Z.le (0)) remainders_l )) (PreH9 : (Forall2 Z.lt remainders_l moduli_l )) (PreH10 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH11 : (1 <= (CRTProduct (moduli_l)))) (PreH12 : ((CRTProduct (moduli_l)) <= 46340)) (PreH13 : (product = (CRTProduct (moduli_l)))) (PreH14 : (1 <= product)) (PreH15 : (product <= 46340)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= result)) (PreH19 : (result < product)) (PreH20 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH21 : (CRTUnprocessedZero moduli_l i result )) ,
  ((( &( "term" ) )) # Int  |->_)
  **  ((( &( "coefficient" ) )) # Int  |-> x_callee_v)
  **  ((( &( "unused" ) )) # Int  |-> y_callee_v)
  **  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  (IntArray.full remainders_pre n_pre remainders_l )
|--
  “ (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) <> (INT64_MIN)) \/ (product <> (-1))) ” 
  &&  “ (product <> 0) ”
.

Definition chinese_remainder_theorem_safety_wit_9 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH2 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH6 : (1 <= (Zlength (moduli_l)))) (PreH7 : (Forall (Z.le (1)) moduli_l )) (PreH8 : (Forall (Z.le (0)) remainders_l )) (PreH9 : (Forall2 Z.lt remainders_l moduli_l )) (PreH10 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH11 : (1 <= (CRTProduct (moduli_l)))) (PreH12 : ((CRTProduct (moduli_l)) <= 46340)) (PreH13 : (product = (CRTProduct (moduli_l)))) (PreH14 : (1 <= product)) (PreH15 : (product <= 46340)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= result)) (PreH19 : (result < product)) (PreH20 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH21 : (CRTUnprocessedZero moduli_l i result )) ,
  ((( &( "term" ) )) # Int  |->_)
  **  ((( &( "coefficient" ) )) # Int  |-> x_callee_v)
  **  ((( &( "unused" ) )) # Int  |-> y_callee_v)
  **  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  (IntArray.full remainders_pre n_pre remainders_l )
|--
  “ ((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (x_callee_v * (product ÷ (Znth i moduli_l 0) ) )) ”
.

Definition chinese_remainder_theorem_safety_wit_10 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH2 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH6 : (1 <= (Zlength (moduli_l)))) (PreH7 : (Forall (Z.le (1)) moduli_l )) (PreH8 : (Forall (Z.le (0)) remainders_l )) (PreH9 : (Forall2 Z.lt remainders_l moduli_l )) (PreH10 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH11 : (1 <= (CRTProduct (moduli_l)))) (PreH12 : ((CRTProduct (moduli_l)) <= 46340)) (PreH13 : (product = (CRTProduct (moduli_l)))) (PreH14 : (1 <= product)) (PreH15 : (product <= 46340)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= result)) (PreH19 : (result < product)) (PreH20 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH21 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  ((( &( "term" ) )) # Int  |-> (signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)))
  **  ((( &( "coefficient" ) )) # Int  |-> x_callee_v)
  **  ((( &( "unused" ) )) # Int  |-> y_callee_v)
  **  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) <> (INT_MIN)) \/ (product <> (-1))) ” 
  &&  “ (product <> 0) ”
.

Definition chinese_remainder_theorem_safety_wit_11 := 
(
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH2 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH6 : (1 <= (Zlength (moduli_l)))) (PreH7 : (Forall (Z.le (1)) moduli_l )) (PreH8 : (Forall (Z.le (0)) remainders_l )) (PreH9 : (Forall2 Z.lt remainders_l moduli_l )) (PreH10 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH11 : (1 <= (CRTProduct (moduli_l)))) (PreH12 : ((CRTProduct (moduli_l)) <= 46340)) (PreH13 : (product = (CRTProduct (moduli_l)))) (PreH14 : (1 <= product)) (PreH15 : (product <= 46340)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= result)) (PreH19 : (result < product)) (PreH20 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH21 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  ((( &( "term" ) )) # Int  |-> (signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)))
  **  ((( &( "coefficient" ) )) # Int  |-> x_callee_v)
  **  ((( &( "unused" ) )) # Int  |-> y_callee_v)
  **  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) )) ”
) \/
(
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH2 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH6 : (1 <= (Zlength (moduli_l)))) (PreH7 : (Forall (Z.le (1)) moduli_l )) (PreH8 : (Forall (Z.le (0)) remainders_l )) (PreH9 : (Forall2 Z.lt remainders_l moduli_l )) (PreH10 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH11 : (1 <= (CRTProduct (moduli_l)))) (PreH12 : ((CRTProduct (moduli_l)) <= 46340)) (PreH13 : (product = (CRTProduct (moduli_l)))) (PreH14 : (1 <= product)) (PreH15 : (product <= 46340)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= result)) (PreH19 : (result < product)) (PreH20 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH21 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  ((( &( "term" ) )) # Int  |-> (signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)))
  **  ((( &( "coefficient" ) )) # Int  |-> x_callee_v)
  **  ((( &( "unused" ) )) # Int  |-> y_callee_v)
  **  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) )) ”
).

Definition chinese_remainder_theorem_safety_wit_11_split_goal_1 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH2 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH6 : (1 <= (Zlength (moduli_l)))) (PreH7 : (Forall (Z.le (1)) moduli_l )) (PreH8 : (Forall (Z.le (0)) remainders_l )) (PreH9 : (Forall2 Z.lt remainders_l moduli_l )) (PreH10 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH11 : (1 <= (CRTProduct (moduli_l)))) (PreH12 : ((CRTProduct (moduli_l)) <= 46340)) (PreH13 : (product = (CRTProduct (moduli_l)))) (PreH14 : (1 <= product)) (PreH15 : (product <= 46340)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= result)) (PreH19 : (result < product)) (PreH20 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH21 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  ((( &( "term" ) )) # Int  |-> (signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)))
  **  ((( &( "coefficient" ) )) # Int  |-> x_callee_v)
  **  ((( &( "unused" ) )) # Int  |-> y_callee_v)
  **  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) <= INT_MAX) ”
.

Definition chinese_remainder_theorem_safety_wit_11_split_goal_2 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH2 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH6 : (1 <= (Zlength (moduli_l)))) (PreH7 : (Forall (Z.le (1)) moduli_l )) (PreH8 : (Forall (Z.le (0)) remainders_l )) (PreH9 : (Forall2 Z.lt remainders_l moduli_l )) (PreH10 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH11 : (1 <= (CRTProduct (moduli_l)))) (PreH12 : ((CRTProduct (moduli_l)) <= 46340)) (PreH13 : (product = (CRTProduct (moduli_l)))) (PreH14 : (1 <= product)) (PreH15 : (product <= 46340)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= result)) (PreH19 : (result < product)) (PreH20 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH21 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  ((( &( "term" ) )) # Int  |-> (signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)))
  **  ((( &( "coefficient" ) )) # Int  |-> x_callee_v)
  **  ((( &( "unused" ) )) # Int  |-> y_callee_v)
  **  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((INT_MIN) <= ((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) )) ”
.

Definition chinese_remainder_theorem_safety_wit_12 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH2 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH6 : (1 <= (Zlength (moduli_l)))) (PreH7 : (Forall (Z.le (1)) moduli_l )) (PreH8 : (Forall (Z.le (0)) remainders_l )) (PreH9 : (Forall2 Z.lt remainders_l moduli_l )) (PreH10 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH11 : (1 <= (CRTProduct (moduli_l)))) (PreH12 : ((CRTProduct (moduli_l)) <= 46340)) (PreH13 : (product = (CRTProduct (moduli_l)))) (PreH14 : (1 <= product)) (PreH15 : (product <= 46340)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= result)) (PreH19 : (result < product)) (PreH20 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH21 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  ((( &( "term" ) )) # Int  |-> (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ))
  **  ((( &( "coefficient" ) )) # Int  |-> x_callee_v)
  **  ((( &( "unused" ) )) # Int  |-> y_callee_v)
  **  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition chinese_remainder_theorem_safety_wit_13 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) < 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  ((( &( "term" ) )) # Int  |-> (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ))
  **  ((( &( "coefficient" ) )) # Int  |-> x_callee_v)
  **  ((( &( "unused" ) )) # Int  |-> y_callee_v)
  **  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) + product ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) + product )) ”
.

Definition chinese_remainder_theorem_safety_wit_14 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) < 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  ((( &( "term" ) )) # Int  |-> ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) + product ))
  **  ((( &( "coefficient" ) )) # Int  |-> x_callee_v)
  **  ((( &( "unused" ) )) # Int  |-> y_callee_v)
  **  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (((result + ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) + product ) ) <> (INT_MIN)) \/ (product <> (-1))) ” 
  &&  “ (product <> 0) ”
.

Definition chinese_remainder_theorem_safety_wit_15 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) < 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  ((( &( "term" ) )) # Int  |-> ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) + product ))
  **  ((( &( "coefficient" ) )) # Int  |-> x_callee_v)
  **  ((( &( "unused" ) )) # Int  |-> y_callee_v)
  **  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((result + ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) + product ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (result + ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) + product ) )) ”
.

Definition chinese_remainder_theorem_safety_wit_16 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) >= 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  ((( &( "term" ) )) # Int  |-> (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ))
  **  ((( &( "coefficient" ) )) # Int  |-> x_callee_v)
  **  ((( &( "unused" ) )) # Int  |-> y_callee_v)
  **  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (((result + (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) ) <> (INT_MIN)) \/ (product <> (-1))) ” 
  &&  “ (product <> 0) ”
.

Definition chinese_remainder_theorem_safety_wit_17 := 
(
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) >= 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  ((( &( "term" ) )) # Int  |-> (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ))
  **  ((( &( "coefficient" ) )) # Int  |-> x_callee_v)
  **  ((( &( "unused" ) )) # Int  |-> y_callee_v)
  **  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((result + (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (result + (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) )) ”
) \/
(
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) >= 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  ((( &( "term" ) )) # Int  |-> (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ))
  **  ((( &( "coefficient" ) )) # Int  |-> x_callee_v)
  **  ((( &( "unused" ) )) # Int  |-> y_callee_v)
  **  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((result + (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (result + (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) )) ”
).

Definition chinese_remainder_theorem_safety_wit_17_split_goal_1 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) >= 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  ((( &( "term" ) )) # Int  |-> (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ))
  **  ((( &( "coefficient" ) )) # Int  |-> x_callee_v)
  **  ((( &( "unused" ) )) # Int  |-> y_callee_v)
  **  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((result + (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) ) <= INT_MAX) ”
.

Definition chinese_remainder_theorem_safety_wit_17_split_goal_2 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) >= 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  ((( &( "term" ) )) # Int  |-> (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ))
  **  ((( &( "coefficient" ) )) # Int  |-> x_callee_v)
  **  ((( &( "unused" ) )) # Int  |-> y_callee_v)
  **  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((INT_MIN) <= (result + (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) )) ”
.

Definition chinese_remainder_theorem_safety_wit_18 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) < 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> ((result + ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) + product ) ) % ( product ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition chinese_remainder_theorem_safety_wit_19 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) >= 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> ((result + (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) ) % ( product ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition chinese_remainder_theorem_entail_wit_1 := 
(
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (PreH1 : (n_pre = (Zlength (moduli_l)))) (PreH2 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH3 : (1 <= (Zlength (moduli_l)))) (PreH4 : (Forall (Z.le (1)) moduli_l )) (PreH5 : (Forall (Z.le (0)) remainders_l )) (PreH6 : (Forall2 Z.lt remainders_l moduli_l )) (PreH7 : forall (j_2: Z) , forall (k_2: Z) , ((((0 <= j_2) /\ (j_2 < k_2)) /\ (k_2 < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j_2) (moduli_l) (0))) ((Znth (k_2) (moduli_l) (0)))) = 1))) (PreH8 : (1 <= (CRTProduct (moduli_l)))) (PreH9 : ((CRTProduct (moduli_l)) <= 46340)) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  (IntArray.full moduli_pre n_pre moduli_l )
|--
  “ (n_pre = (Zlength (moduli_l))) ” 
  &&  “ ((Zlength (remainders_l)) = (Zlength (moduli_l))) ” 
  &&  “ (1 <= (Zlength (moduli_l))) ” 
  &&  “ (Forall (Z.le (1)) moduli_l ) ” 
  &&  “ (Forall (Z.le (0)) remainders_l ) ” 
  &&  “ (Forall2 Z.lt remainders_l moduli_l ) ” 
  &&  “ forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1)) ” 
  &&  “ (1 <= (CRTProduct (moduli_l))) ” 
  &&  “ ((CRTProduct (moduli_l)) <= 46340) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (1 = (CRTProduct ((sublist (0) (0) (moduli_l))))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (CRTProduct (moduli_l))) ”
  &&  (IntArray.full remainders_pre n_pre remainders_l )
  **  (IntArray.full moduli_pre n_pre moduli_l )
) \/
(
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (PreH1 : (n_pre = (Zlength (moduli_l)))) (PreH2 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH3 : (1 <= (Zlength (moduli_l)))) (PreH4 : (Forall (Z.le (1)) moduli_l )) (PreH5 : (Forall (Z.le (0)) remainders_l )) (PreH6 : (Forall2 Z.lt remainders_l moduli_l )) (PreH7 : forall (j_2: Z) , forall (k_2: Z) , ((((0 <= j_2) /\ (j_2 < k_2)) /\ (k_2 < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j_2) (moduli_l) (0))) ((Znth (k_2) (moduli_l) (0)))) = 1))) (PreH8 : (1 <= (CRTProduct (moduli_l)))) (PreH9 : ((CRTProduct (moduli_l)) <= 46340)) ,
  TT && emp 
|--
  “ (1 = (CRTProduct ((sublist (0) (0) (moduli_l))))) ” 
  &&  “ forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1)) ”
  &&  emp
).

Definition chinese_remainder_theorem_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (PreH1 : (n_pre = (Zlength (moduli_l)))) (PreH2 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH3 : (1 <= (Zlength (moduli_l)))) (PreH4 : (Forall (Z.le (1)) moduli_l )) (PreH5 : (Forall (Z.le (0)) remainders_l )) (PreH6 : (Forall2 Z.lt remainders_l moduli_l )) (PreH7 : forall (j_2: Z) , forall (k_2: Z) , ((((0 <= j_2) /\ (j_2 < k_2)) /\ (k_2 < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j_2) (moduli_l) (0))) ((Znth (k_2) (moduli_l) (0)))) = 1))) (PreH8 : (1 <= (CRTProduct (moduli_l)))) (PreH9 : ((CRTProduct (moduli_l)) <= 46340)) ,
  (1 = (CRTProduct ((sublist (0) (0) (moduli_l)))))
.

Definition chinese_remainder_theorem_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (PreH1 : (n_pre = (Zlength (moduli_l)))) (PreH2 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH3 : (1 <= (Zlength (moduli_l)))) (PreH4 : (Forall (Z.le (1)) moduli_l )) (PreH5 : (Forall (Z.le (0)) remainders_l )) (PreH6 : (Forall2 Z.lt remainders_l moduli_l )) (PreH7 : forall (j_2: Z) , forall (k_2: Z) , ((((0 <= j_2) /\ (j_2 < k_2)) /\ (k_2 < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j_2) (moduli_l) (0))) ((Znth (k_2) (moduli_l) (0)))) = 1))) (PreH8 : (1 <= (CRTProduct (moduli_l)))) (PreH9 : ((CRTProduct (moduli_l)) <= 46340)) ,
  forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))
.

Definition chinese_remainder_theorem_entail_wit_2 := 
(
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (product: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (product = (CRTProduct ((sublist (0) (i) (moduli_l)))))) (PreH14 : (1 <= product)) (PreH15 : (product <= (CRTProduct (moduli_l)))) ,
  (IntArray.full moduli_pre n_pre moduli_l )
  **  (IntArray.full remainders_pre n_pre remainders_l )
|--
  “ (n_pre = (Zlength (moduli_l))) ” 
  &&  “ ((Zlength (remainders_l)) = (Zlength (moduli_l))) ” 
  &&  “ (1 <= (Zlength (moduli_l))) ” 
  &&  “ (Forall (Z.le (1)) moduli_l ) ” 
  &&  “ (Forall (Z.le (0)) remainders_l ) ” 
  &&  “ (Forall2 Z.lt remainders_l moduli_l ) ” 
  &&  “ forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1)) ” 
  &&  “ (1 <= (CRTProduct (moduli_l))) ” 
  &&  “ ((CRTProduct (moduli_l)) <= 46340) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((product * (Znth i moduli_l 0) ) = (CRTProduct ((sublist (0) ((i + 1 )) (moduli_l))))) ” 
  &&  “ (1 <= (product * (Znth i moduli_l 0) )) ” 
  &&  “ ((product * (Znth i moduli_l 0) ) <= (CRTProduct (moduli_l))) ”
  &&  (IntArray.full remainders_pre n_pre remainders_l )
  **  (IntArray.full moduli_pre n_pre moduli_l )
) \/
(
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (product: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (product = (CRTProduct ((sublist (0) (i) (moduli_l)))))) (PreH14 : (1 <= product)) (PreH15 : (product <= (CRTProduct (moduli_l)))) ,
  TT && emp 
|--
  “ ((product * (Znth i moduli_l 0) ) <= (CRTProduct (moduli_l))) ” 
  &&  “ (1 <= (product * (Znth i moduli_l 0) )) ” 
  &&  “ ((product * (Znth i moduli_l 0) ) = (CRTProduct ((sublist (0) ((i + 1 )) (moduli_l))))) ”
  &&  emp
).

Definition chinese_remainder_theorem_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (product: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (product = (CRTProduct ((sublist (0) (i) (moduli_l)))))) (PreH14 : (1 <= product)) (PreH15 : (product <= (CRTProduct (moduli_l)))) ,
  ((product * (Znth i moduli_l 0) ) <= (CRTProduct (moduli_l)))
.

Definition chinese_remainder_theorem_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (product: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (product = (CRTProduct ((sublist (0) (i) (moduli_l)))))) (PreH14 : (1 <= product)) (PreH15 : (product <= (CRTProduct (moduli_l)))) ,
  (1 <= (product * (Znth i moduli_l 0) ))
.

Definition chinese_remainder_theorem_entail_wit_2_split_goal_3 := 
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (product: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (product = (CRTProduct ((sublist (0) (i) (moduli_l)))))) (PreH14 : (1 <= product)) (PreH15 : (product <= (CRTProduct (moduli_l)))) ,
  ((product * (Znth i moduli_l 0) ) = (CRTProduct ((sublist (0) ((i + 1 )) (moduli_l)))))
.

Definition chinese_remainder_theorem_entail_wit_3 := 
(
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (product: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j_2: Z) , forall (k_2: Z) , ((((0 <= j_2) /\ (j_2 < k_2)) /\ (k_2 < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j_2) (moduli_l) (0))) ((Znth (k_2) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (product = (CRTProduct ((sublist (0) (i) (moduli_l)))))) (PreH14 : (1 <= product)) (PreH15 : (product <= (CRTProduct (moduli_l)))) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  (IntArray.full moduli_pre n_pre moduli_l )
|--
  “ (n_pre = (Zlength (moduli_l))) ” 
  &&  “ ((Zlength (remainders_l)) = (Zlength (moduli_l))) ” 
  &&  “ (1 <= (Zlength (moduli_l))) ” 
  &&  “ (Forall (Z.le (1)) moduli_l ) ” 
  &&  “ (Forall (Z.le (0)) remainders_l ) ” 
  &&  “ (Forall2 Z.lt remainders_l moduli_l ) ” 
  &&  “ forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1)) ” 
  &&  “ (1 <= (CRTProduct (moduli_l))) ” 
  &&  “ ((CRTProduct (moduli_l)) <= 46340) ” 
  &&  “ (product = (CRTProduct (moduli_l))) ” 
  &&  “ (1 <= product) ” 
  &&  “ (product <= 46340) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < product) ” 
  &&  “ (CRTConsistentPrefix remainders_l moduli_l 0 0 ) ” 
  &&  “ (CRTUnprocessedZero moduli_l 0 0 ) ”
  &&  (IntArray.full remainders_pre n_pre remainders_l )
  **  (IntArray.full moduli_pre n_pre moduli_l )
) \/
(
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (product: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j_2: Z) , forall (k_2: Z) , ((((0 <= j_2) /\ (j_2 < k_2)) /\ (k_2 < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j_2) (moduli_l) (0))) ((Znth (k_2) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (product = (CRTProduct ((sublist (0) (i) (moduli_l)))))) (PreH14 : (1 <= product)) (PreH15 : (product <= (CRTProduct (moduli_l)))) ,
  TT && emp 
|--
  “ (CRTUnprocessedZero moduli_l 0 0 ) ” 
  &&  “ (CRTConsistentPrefix remainders_l moduli_l 0 0 ) ” 
  &&  “ (product = (CRTProduct (moduli_l))) ” 
  &&  “ forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1)) ”
  &&  emp
).

Definition chinese_remainder_theorem_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (product: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j_2: Z) , forall (k_2: Z) , ((((0 <= j_2) /\ (j_2 < k_2)) /\ (k_2 < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j_2) (moduli_l) (0))) ((Znth (k_2) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (product = (CRTProduct ((sublist (0) (i) (moduli_l)))))) (PreH14 : (1 <= product)) (PreH15 : (product <= (CRTProduct (moduli_l)))) ,
  (CRTUnprocessedZero moduli_l 0 0 )
.

Definition chinese_remainder_theorem_entail_wit_3_split_goal_2 := 
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (product: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j_2: Z) , forall (k_2: Z) , ((((0 <= j_2) /\ (j_2 < k_2)) /\ (k_2 < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j_2) (moduli_l) (0))) ((Znth (k_2) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (product = (CRTProduct ((sublist (0) (i) (moduli_l)))))) (PreH14 : (1 <= product)) (PreH15 : (product <= (CRTProduct (moduli_l)))) ,
  (CRTConsistentPrefix remainders_l moduli_l 0 0 )
.

Definition chinese_remainder_theorem_entail_wit_3_split_goal_3 := 
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (product: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j_2: Z) , forall (k_2: Z) , ((((0 <= j_2) /\ (j_2 < k_2)) /\ (k_2 < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j_2) (moduli_l) (0))) ((Znth (k_2) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (product = (CRTProduct ((sublist (0) (i) (moduli_l)))))) (PreH14 : (1 <= product)) (PreH15 : (product <= (CRTProduct (moduli_l)))) ,
  (product = (CRTProduct (moduli_l)))
.

Definition chinese_remainder_theorem_entail_wit_3_split_goal_4 := 
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (product: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j_2: Z) , forall (k_2: Z) , ((((0 <= j_2) /\ (j_2 < k_2)) /\ (k_2 < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j_2) (moduli_l) (0))) ((Znth (k_2) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (product = (CRTProduct ((sublist (0) (i) (moduli_l)))))) (PreH14 : (1 <= product)) (PreH15 : (product <= (CRTProduct (moduli_l)))) ,
  forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))
.

Definition chinese_remainder_theorem_entail_wit_4_1 := 
(
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) < 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  (IntArray.full moduli_pre n_pre moduli_l )
|--
  “ (n_pre = (Zlength (moduli_l))) ” 
  &&  “ ((Zlength (remainders_l)) = (Zlength (moduli_l))) ” 
  &&  “ (1 <= (Zlength (moduli_l))) ” 
  &&  “ (Forall (Z.le (1)) moduli_l ) ” 
  &&  “ (Forall (Z.le (0)) remainders_l ) ” 
  &&  “ (Forall2 Z.lt remainders_l moduli_l ) ” 
  &&  “ forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1)) ” 
  &&  “ (1 <= (CRTProduct (moduli_l))) ” 
  &&  “ ((CRTProduct (moduli_l)) <= 46340) ” 
  &&  “ (product = (CRTProduct (moduli_l))) ” 
  &&  “ (1 <= product) ” 
  &&  “ (product <= 46340) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= ((result + ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) + product ) ) % ( product ) )) ” 
  &&  “ (((result + ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) + product ) ) % ( product ) ) < product) ” 
  &&  “ (CRTConsistentPrefix remainders_l moduli_l (i + 1 ) ((result + ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) + product ) ) % ( product ) ) ) ” 
  &&  “ (CRTUnprocessedZero moduli_l (i + 1 ) ((result + ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) + product ) ) % ( product ) ) ) ”
  &&  (IntArray.full remainders_pre n_pre remainders_l )
  **  (IntArray.full moduli_pre n_pre moduli_l )
) \/
(
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) < 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  TT && emp 
|--
  “ (CRTUnprocessedZero moduli_l (i + 1 ) ((result + ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) + product ) ) % ( product ) ) ) ” 
  &&  “ (CRTConsistentPrefix remainders_l moduli_l (i + 1 ) ((result + ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) + product ) ) % ( product ) ) ) ” 
  &&  “ (((result + ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) + product ) ) % ( product ) ) < product) ” 
  &&  “ (0 <= ((result + ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) + product ) ) % ( product ) )) ”
  &&  emp
).

Definition chinese_remainder_theorem_entail_wit_4_1_split_goal_1 := 
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) < 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  (CRTUnprocessedZero moduli_l (i + 1 ) ((result + ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) + product ) ) % ( product ) ) )
.

Definition chinese_remainder_theorem_entail_wit_4_1_split_goal_2 := 
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) < 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  (CRTConsistentPrefix remainders_l moduli_l (i + 1 ) ((result + ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) + product ) ) % ( product ) ) )
.

Definition chinese_remainder_theorem_entail_wit_4_1_split_goal_3 := 
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) < 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  (((result + ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) + product ) ) % ( product ) ) < product)
.

Definition chinese_remainder_theorem_entail_wit_4_1_split_goal_4 := 
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) < 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  (0 <= ((result + ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) + product ) ) % ( product ) ))
.

Definition chinese_remainder_theorem_entail_wit_4_2 := 
(
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) >= 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  (IntArray.full moduli_pre n_pre moduli_l )
|--
  “ (n_pre = (Zlength (moduli_l))) ” 
  &&  “ ((Zlength (remainders_l)) = (Zlength (moduli_l))) ” 
  &&  “ (1 <= (Zlength (moduli_l))) ” 
  &&  “ (Forall (Z.le (1)) moduli_l ) ” 
  &&  “ (Forall (Z.le (0)) remainders_l ) ” 
  &&  “ (Forall2 Z.lt remainders_l moduli_l ) ” 
  &&  “ forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1)) ” 
  &&  “ (1 <= (CRTProduct (moduli_l))) ” 
  &&  “ ((CRTProduct (moduli_l)) <= 46340) ” 
  &&  “ (product = (CRTProduct (moduli_l))) ” 
  &&  “ (1 <= product) ” 
  &&  “ (product <= 46340) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= ((result + (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) ) % ( product ) )) ” 
  &&  “ (((result + (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) ) % ( product ) ) < product) ” 
  &&  “ (CRTConsistentPrefix remainders_l moduli_l (i + 1 ) ((result + (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) ) % ( product ) ) ) ” 
  &&  “ (CRTUnprocessedZero moduli_l (i + 1 ) ((result + (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) ) % ( product ) ) ) ”
  &&  (IntArray.full remainders_pre n_pre remainders_l )
  **  (IntArray.full moduli_pre n_pre moduli_l )
) \/
(
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) >= 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  TT && emp 
|--
  “ (CRTUnprocessedZero moduli_l (i + 1 ) ((result + (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) ) % ( product ) ) ) ” 
  &&  “ (CRTConsistentPrefix remainders_l moduli_l (i + 1 ) ((result + (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) ) % ( product ) ) ) ” 
  &&  “ (((result + (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) ) % ( product ) ) < product) ” 
  &&  “ (0 <= ((result + (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) ) % ( product ) )) ”
  &&  emp
).

Definition chinese_remainder_theorem_entail_wit_4_2_split_goal_1 := 
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) >= 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  (CRTUnprocessedZero moduli_l (i + 1 ) ((result + (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) ) % ( product ) ) )
.

Definition chinese_remainder_theorem_entail_wit_4_2_split_goal_2 := 
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) >= 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  (CRTConsistentPrefix remainders_l moduli_l (i + 1 ) ((result + (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) ) % ( product ) ) )
.

Definition chinese_remainder_theorem_entail_wit_4_2_split_goal_3 := 
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) >= 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  (((result + (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) ) % ( product ) ) < product)
.

Definition chinese_remainder_theorem_entail_wit_4_2_split_goal_4 := 
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : ((((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) >= 0)) (PreH2 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH4 : (i < n_pre)) (PreH5 : (n_pre = (Zlength (moduli_l)))) (PreH6 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH7 : (1 <= (Zlength (moduli_l)))) (PreH8 : (Forall (Z.le (1)) moduli_l )) (PreH9 : (Forall (Z.le (0)) remainders_l )) (PreH10 : (Forall2 Z.lt remainders_l moduli_l )) (PreH11 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH12 : (1 <= (CRTProduct (moduli_l)))) (PreH13 : ((CRTProduct (moduli_l)) <= 46340)) (PreH14 : (product = (CRTProduct (moduli_l)))) (PreH15 : (1 <= product)) (PreH16 : (product <= 46340)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < product)) (PreH21 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH22 : (CRTUnprocessedZero moduli_l i result )) ,
  (0 <= ((result + (((signed_last_nbits (((x_callee_v * (product ÷ (Znth i moduli_l 0) ) ) % ( product ) )) (32)) * (Znth i remainders_l 0) ) % ( product ) ) ) % ( product ) ))
.

Definition chinese_remainder_theorem_return_wit_1 := 
(
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (product = (CRTProduct (moduli_l)))) (PreH12 : (1 <= product)) (PreH13 : (product <= 46340)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= result)) (PreH17 : (result < product)) (PreH18 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH19 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  (IntArray.full moduli_pre n_pre moduli_l )
|--
  “ (CanonicalCRTSolution remainders_l moduli_l result ) ”
  &&  (IntArray.full remainders_pre n_pre remainders_l )
  **  (IntArray.full moduli_pre n_pre moduli_l )
) \/
(
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (product = (CRTProduct (moduli_l)))) (PreH12 : (1 <= product)) (PreH13 : (product <= 46340)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= result)) (PreH17 : (result < product)) (PreH18 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH19 : (CRTUnprocessedZero moduli_l i result )) ,
  TT && emp 
|--
  “ (CanonicalCRTSolution remainders_l moduli_l result ) ”
  &&  emp
).

Definition chinese_remainder_theorem_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (product = (CRTProduct (moduli_l)))) (PreH12 : (1 <= product)) (PreH13 : (product <= 46340)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= result)) (PreH17 : (result < product)) (PreH18 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH19 : (CRTUnprocessedZero moduli_l i result )) ,
  (CanonicalCRTSolution remainders_l moduli_l result )
.

Definition chinese_remainder_theorem_partial_solve_wit_1 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (product: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (product = (CRTProduct ((sublist (0) (i) (moduli_l)))))) (PreH14 : (1 <= product)) (PreH15 : (product <= (CRTProduct (moduli_l)))) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  (IntArray.full moduli_pre n_pre moduli_l )
|--
  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (moduli_l))) ” 
  &&  “ ((Zlength (remainders_l)) = (Zlength (moduli_l))) ” 
  &&  “ (1 <= (Zlength (moduli_l))) ” 
  &&  “ (Forall (Z.le (1)) moduli_l ) ” 
  &&  “ (Forall (Z.le (0)) remainders_l ) ” 
  &&  “ (Forall2 Z.lt remainders_l moduli_l ) ” 
  &&  “ forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1)) ” 
  &&  “ (1 <= (CRTProduct (moduli_l))) ” 
  &&  “ ((CRTProduct (moduli_l)) <= 46340) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (product = (CRTProduct ((sublist (0) (i) (moduli_l))))) ” 
  &&  “ (1 <= product) ” 
  &&  “ (product <= (CRTProduct (moduli_l))) ”
  &&  (((moduli_pre + (i * sizeof(INT)))) # Int  |-> (Znth i moduli_l 0))
  **  (IntArray.missing_i moduli_pre i 0 n_pre moduli_l )
  **  (IntArray.full remainders_pre n_pre remainders_l )
.

Definition chinese_remainder_theorem_partial_solve_wit_2 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (product = (CRTProduct (moduli_l)))) (PreH12 : (1 <= product)) (PreH13 : (product <= 46340)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= result)) (PreH17 : (result < product)) (PreH18 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH19 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full remainders_pre n_pre remainders_l )
  **  (IntArray.full moduli_pre n_pre moduli_l )
|--
  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (moduli_l))) ” 
  &&  “ ((Zlength (remainders_l)) = (Zlength (moduli_l))) ” 
  &&  “ (1 <= (Zlength (moduli_l))) ” 
  &&  “ (Forall (Z.le (1)) moduli_l ) ” 
  &&  “ (Forall (Z.le (0)) remainders_l ) ” 
  &&  “ (Forall2 Z.lt remainders_l moduli_l ) ” 
  &&  “ forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1)) ” 
  &&  “ (1 <= (CRTProduct (moduli_l))) ” 
  &&  “ ((CRTProduct (moduli_l)) <= 46340) ” 
  &&  “ (product = (CRTProduct (moduli_l))) ” 
  &&  “ (1 <= product) ” 
  &&  “ (product <= 46340) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= result) ” 
  &&  “ (result < product) ” 
  &&  “ (CRTConsistentPrefix remainders_l moduli_l i result ) ” 
  &&  “ (CRTUnprocessedZero moduli_l i result ) ”
  &&  (((moduli_pre + (i * sizeof(INT)))) # Int  |-> (Znth i moduli_l 0))
  **  (IntArray.missing_i moduli_pre i 0 n_pre moduli_l )
  **  (IntArray.full remainders_pre n_pre remainders_l )
.

Definition chinese_remainder_theorem_partial_solve_wit_3 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (product = (CRTProduct (moduli_l)))) (PreH12 : (1 <= product)) (PreH13 : (product <= 46340)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= result)) (PreH17 : (result < product)) (PreH18 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH19 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full moduli_pre n_pre moduli_l )
  **  (IntArray.full remainders_pre n_pre remainders_l )
|--
  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (moduli_l))) ” 
  &&  “ ((Zlength (remainders_l)) = (Zlength (moduli_l))) ” 
  &&  “ (1 <= (Zlength (moduli_l))) ” 
  &&  “ (Forall (Z.le (1)) moduli_l ) ” 
  &&  “ (Forall (Z.le (0)) remainders_l ) ” 
  &&  “ (Forall2 Z.lt remainders_l moduli_l ) ” 
  &&  “ forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1)) ” 
  &&  “ (1 <= (CRTProduct (moduli_l))) ” 
  &&  “ ((CRTProduct (moduli_l)) <= 46340) ” 
  &&  “ (product = (CRTProduct (moduli_l))) ” 
  &&  “ (1 <= product) ” 
  &&  “ (product <= 46340) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= result) ” 
  &&  “ (result < product) ” 
  &&  “ (CRTConsistentPrefix remainders_l moduli_l i result ) ” 
  &&  “ (CRTUnprocessedZero moduli_l i result ) ”
  &&  (((moduli_pre + (i * sizeof(INT)))) # Int  |-> (Znth i moduli_l 0))
  **  (IntArray.missing_i moduli_pre i 0 n_pre moduli_l )
  **  (IntArray.full remainders_pre n_pre remainders_l )
.

Definition chinese_remainder_theorem_partial_solve_wit_4_pure := 
(
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (product = (CRTProduct (moduli_l)))) (PreH12 : (1 <= product)) (PreH13 : (product <= 46340)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= result)) (PreH17 : (result < product)) (PreH18 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH19 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "unused" ) )) # Int  |->_)
  **  ((( &( "coefficient" ) )) # Int  |->_)
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  (IntArray.full remainders_pre n_pre remainders_l )
|--
  “ ((Znth i moduli_l 0) <= INT_MAX) ” 
  &&  “ (INT_MIN < (Znth i moduli_l 0)) ” 
  &&  “ ((product ÷ (Znth i moduli_l 0) ) <= INT_MAX) ” 
  &&  “ (INT_MIN < (product ÷ (Znth i moduli_l 0) )) ”
) \/
(
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (PreH1 : (result <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (product <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((product ÷ (Znth i moduli_l 0) ) <= INT_MAX)) (PreH6 : (result >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (product >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((product ÷ (Znth i moduli_l 0) ) >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (n_pre = (Zlength (moduli_l)))) (PreH13 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH14 : (1 <= (Zlength (moduli_l)))) (PreH15 : (Forall (Z.le (1)) moduli_l )) (PreH16 : (Forall (Z.le (0)) remainders_l )) (PreH17 : (Forall2 Z.lt remainders_l moduli_l )) (PreH18 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH19 : (1 <= (CRTProduct (moduli_l)))) (PreH20 : ((CRTProduct (moduli_l)) <= 46340)) (PreH21 : (product = (CRTProduct (moduli_l)))) (PreH22 : (1 <= product)) (PreH23 : (product <= 46340)) (PreH24 : (0 <= i)) (PreH25 : (i <= n_pre)) (PreH26 : (0 <= result)) (PreH27 : (result < product)) (PreH28 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH29 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "unused" ) )) # Int  |->_)
  **  ((( &( "coefficient" ) )) # Int  |->_)
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  (IntArray.full remainders_pre n_pre remainders_l )
|--
  “ (INT_MIN < (product ÷ (Znth i moduli_l 0) )) ” 
  &&  “ (INT_MIN < (Znth i moduli_l 0)) ” 
  &&  “ ((Znth i moduli_l 0) <= INT_MAX) ”
).

Definition chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (PreH1 : (result <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (product <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((product ÷ (Znth i moduli_l 0) ) <= INT_MAX)) (PreH6 : (result >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (product >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((product ÷ (Znth i moduli_l 0) ) >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (n_pre = (Zlength (moduli_l)))) (PreH13 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH14 : (1 <= (Zlength (moduli_l)))) (PreH15 : (Forall (Z.le (1)) moduli_l )) (PreH16 : (Forall (Z.le (0)) remainders_l )) (PreH17 : (Forall2 Z.lt remainders_l moduli_l )) (PreH18 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH19 : (1 <= (CRTProduct (moduli_l)))) (PreH20 : ((CRTProduct (moduli_l)) <= 46340)) (PreH21 : (product = (CRTProduct (moduli_l)))) (PreH22 : (1 <= product)) (PreH23 : (product <= 46340)) (PreH24 : (0 <= i)) (PreH25 : (i <= n_pre)) (PreH26 : (0 <= result)) (PreH27 : (result < product)) (PreH28 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH29 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "unused" ) )) # Int  |->_)
  **  ((( &( "coefficient" ) )) # Int  |->_)
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  (IntArray.full remainders_pre n_pre remainders_l )
|--
  “ (INT_MIN < (product ÷ (Znth i moduli_l 0) )) ”
.

Definition chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (PreH1 : (result <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (product <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((product ÷ (Znth i moduli_l 0) ) <= INT_MAX)) (PreH6 : (result >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (product >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((product ÷ (Znth i moduli_l 0) ) >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (n_pre = (Zlength (moduli_l)))) (PreH13 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH14 : (1 <= (Zlength (moduli_l)))) (PreH15 : (Forall (Z.le (1)) moduli_l )) (PreH16 : (Forall (Z.le (0)) remainders_l )) (PreH17 : (Forall2 Z.lt remainders_l moduli_l )) (PreH18 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH19 : (1 <= (CRTProduct (moduli_l)))) (PreH20 : ((CRTProduct (moduli_l)) <= 46340)) (PreH21 : (product = (CRTProduct (moduli_l)))) (PreH22 : (1 <= product)) (PreH23 : (product <= 46340)) (PreH24 : (0 <= i)) (PreH25 : (i <= n_pre)) (PreH26 : (0 <= result)) (PreH27 : (result < product)) (PreH28 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH29 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "unused" ) )) # Int  |->_)
  **  ((( &( "coefficient" ) )) # Int  |->_)
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  (IntArray.full remainders_pre n_pre remainders_l )
|--
  “ (INT_MIN < (Znth i moduli_l 0)) ”
.

Definition chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_3 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (PreH1 : (result <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (product <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((product ÷ (Znth i moduli_l 0) ) <= INT_MAX)) (PreH6 : (result >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (product >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((product ÷ (Znth i moduli_l 0) ) >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (n_pre = (Zlength (moduli_l)))) (PreH13 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH14 : (1 <= (Zlength (moduli_l)))) (PreH15 : (Forall (Z.le (1)) moduli_l )) (PreH16 : (Forall (Z.le (0)) remainders_l )) (PreH17 : (Forall2 Z.lt remainders_l moduli_l )) (PreH18 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH19 : (1 <= (CRTProduct (moduli_l)))) (PreH20 : ((CRTProduct (moduli_l)) <= 46340)) (PreH21 : (product = (CRTProduct (moduli_l)))) (PreH22 : (1 <= product)) (PreH23 : (product <= 46340)) (PreH24 : (0 <= i)) (PreH25 : (i <= n_pre)) (PreH26 : (0 <= result)) (PreH27 : (result < product)) (PreH28 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH29 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full moduli_pre n_pre moduli_l )
  **  ((( &( "unused" ) )) # Int  |->_)
  **  ((( &( "coefficient" ) )) # Int  |->_)
  **  ((( &( "partial_product" ) )) # Int  |-> (product ÷ (Znth i moduli_l 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "remainders" ) )) # Ptr  |-> remainders_pre)
  **  ((( &( "moduli" ) )) # Ptr  |-> moduli_pre)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  (IntArray.full remainders_pre n_pre remainders_l )
|--
  “ ((Znth i moduli_l 0) <= INT_MAX) ”
.

Definition chinese_remainder_theorem_partial_solve_wit_4_aux := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (moduli_l)))) (PreH3 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH4 : (1 <= (Zlength (moduli_l)))) (PreH5 : (Forall (Z.le (1)) moduli_l )) (PreH6 : (Forall (Z.le (0)) remainders_l )) (PreH7 : (Forall2 Z.lt remainders_l moduli_l )) (PreH8 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH9 : (1 <= (CRTProduct (moduli_l)))) (PreH10 : ((CRTProduct (moduli_l)) <= 46340)) (PreH11 : (product = (CRTProduct (moduli_l)))) (PreH12 : (1 <= product)) (PreH13 : (product <= 46340)) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (0 <= result)) (PreH17 : (result < product)) (PreH18 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH19 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full moduli_pre n_pre moduli_l )
  **  (IntArray.full remainders_pre n_pre remainders_l )
|--
  “ ((Znth i moduli_l 0) <= INT_MAX) ” 
  &&  “ (INT_MIN < (Znth i moduli_l 0)) ” 
  &&  “ ((product ÷ (Znth i moduli_l 0) ) <= INT_MAX) ” 
  &&  “ (INT_MIN < (product ÷ (Znth i moduli_l 0) )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (moduli_l))) ” 
  &&  “ ((Zlength (remainders_l)) = (Zlength (moduli_l))) ” 
  &&  “ (1 <= (Zlength (moduli_l))) ” 
  &&  “ (Forall (Z.le (1)) moduli_l ) ” 
  &&  “ (Forall (Z.le (0)) remainders_l ) ” 
  &&  “ (Forall2 Z.lt remainders_l moduli_l ) ” 
  &&  “ forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1)) ” 
  &&  “ (1 <= (CRTProduct (moduli_l))) ” 
  &&  “ ((CRTProduct (moduli_l)) <= 46340) ” 
  &&  “ (product = (CRTProduct (moduli_l))) ” 
  &&  “ (1 <= product) ” 
  &&  “ (product <= 46340) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= result) ” 
  &&  “ (result < product) ” 
  &&  “ (CRTConsistentPrefix remainders_l moduli_l i result ) ” 
  &&  “ (CRTUnprocessedZero moduli_l i result ) ”
  &&  (IntArray.full moduli_pre n_pre moduli_l )
  **  (IntArray.full remainders_pre n_pre remainders_l )
.

Definition chinese_remainder_theorem_partial_solve_wit_4 := chinese_remainder_theorem_partial_solve_wit_4_pure -> chinese_remainder_theorem_partial_solve_wit_4_aux.

Definition chinese_remainder_theorem_partial_solve_wit_5 := 
forall (moduli_pre: Z) (remainders_pre: Z) (n_pre: Z) (moduli_l: (@list Z)) (remainders_l: (@list Z)) (result: Z) (i: Z) (product: Z) (y_callee_v: Z) (x_callee_v: Z) (retval: Z) (PreH1 : (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH2 : ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0))))) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (moduli_l)))) (PreH5 : ((Zlength (remainders_l)) = (Zlength (moduli_l)))) (PreH6 : (1 <= (Zlength (moduli_l)))) (PreH7 : (Forall (Z.le (1)) moduli_l )) (PreH8 : (Forall (Z.le (0)) remainders_l )) (PreH9 : (Forall2 Z.lt remainders_l moduli_l )) (PreH10 : forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1))) (PreH11 : (1 <= (CRTProduct (moduli_l)))) (PreH12 : ((CRTProduct (moduli_l)) <= 46340)) (PreH13 : (product = (CRTProduct (moduli_l)))) (PreH14 : (1 <= product)) (PreH15 : (product <= 46340)) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (0 <= result)) (PreH19 : (result < product)) (PreH20 : (CRTConsistentPrefix remainders_l moduli_l i result )) (PreH21 : (CRTUnprocessedZero moduli_l i result )) ,
  (IntArray.full moduli_pre n_pre moduli_l )
  **  (IntArray.full remainders_pre n_pre remainders_l )
|--
  “ (retval = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0)))) ” 
  &&  “ ((((product ÷ (Znth i moduli_l 0) ) * x_callee_v ) + ((Znth i moduli_l 0) * y_callee_v ) ) = (Zgcd ((product ÷ (Znth i moduli_l 0) )) ((Znth i moduli_l 0)))) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (moduli_l))) ” 
  &&  “ ((Zlength (remainders_l)) = (Zlength (moduli_l))) ” 
  &&  “ (1 <= (Zlength (moduli_l))) ” 
  &&  “ (Forall (Z.le (1)) moduli_l ) ” 
  &&  “ (Forall (Z.le (0)) remainders_l ) ” 
  &&  “ (Forall2 Z.lt remainders_l moduli_l ) ” 
  &&  “ forall (j: Z) , forall (k: Z) , ((((0 <= j) /\ (j < k)) /\ (k < (Zlength (moduli_l)))) -> ((Zgcd ((Znth (j) (moduli_l) (0))) ((Znth (k) (moduli_l) (0)))) = 1)) ” 
  &&  “ (1 <= (CRTProduct (moduli_l))) ” 
  &&  “ ((CRTProduct (moduli_l)) <= 46340) ” 
  &&  “ (product = (CRTProduct (moduli_l))) ” 
  &&  “ (1 <= product) ” 
  &&  “ (product <= 46340) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= result) ” 
  &&  “ (result < product) ” 
  &&  “ (CRTConsistentPrefix remainders_l moduli_l i result ) ” 
  &&  “ (CRTUnprocessedZero moduli_l i result ) ”
  &&  (((remainders_pre + (i * sizeof(INT)))) # Int  |-> (Znth i remainders_l 0))
  **  (IntArray.missing_i remainders_pre i 0 n_pre remainders_l )
  **  (IntArray.full moduli_pre n_pre moduli_l )
.

Module Type VC_Correct.


Axiom proof_of_chinese_remainder_theorem_safety_wit_1 : chinese_remainder_theorem_safety_wit_1.
Axiom proof_of_chinese_remainder_theorem_safety_wit_2 : chinese_remainder_theorem_safety_wit_2.
Axiom proof_of_chinese_remainder_theorem_safety_wit_3 : chinese_remainder_theorem_safety_wit_3.
Axiom proof_of_chinese_remainder_theorem_safety_wit_4 : chinese_remainder_theorem_safety_wit_4.
Axiom proof_of_chinese_remainder_theorem_safety_wit_5 : chinese_remainder_theorem_safety_wit_5.
Axiom proof_of_chinese_remainder_theorem_safety_wit_6 : chinese_remainder_theorem_safety_wit_6.
Axiom proof_of_chinese_remainder_theorem_safety_wit_7 : chinese_remainder_theorem_safety_wit_7.
Axiom proof_of_chinese_remainder_theorem_safety_wit_8 : chinese_remainder_theorem_safety_wit_8.
Axiom proof_of_chinese_remainder_theorem_safety_wit_9 : chinese_remainder_theorem_safety_wit_9.
Axiom proof_of_chinese_remainder_theorem_safety_wit_10 : chinese_remainder_theorem_safety_wit_10.
Axiom proof_of_chinese_remainder_theorem_safety_wit_11 : chinese_remainder_theorem_safety_wit_11.
Axiom proof_of_chinese_remainder_theorem_safety_wit_12 : chinese_remainder_theorem_safety_wit_12.
Axiom proof_of_chinese_remainder_theorem_safety_wit_13 : chinese_remainder_theorem_safety_wit_13.
Axiom proof_of_chinese_remainder_theorem_safety_wit_14 : chinese_remainder_theorem_safety_wit_14.
Axiom proof_of_chinese_remainder_theorem_safety_wit_15 : chinese_remainder_theorem_safety_wit_15.
Axiom proof_of_chinese_remainder_theorem_safety_wit_16 : chinese_remainder_theorem_safety_wit_16.
Axiom proof_of_chinese_remainder_theorem_safety_wit_17 : chinese_remainder_theorem_safety_wit_17.
Axiom proof_of_chinese_remainder_theorem_safety_wit_18 : chinese_remainder_theorem_safety_wit_18.
Axiom proof_of_chinese_remainder_theorem_safety_wit_19 : chinese_remainder_theorem_safety_wit_19.
Axiom proof_of_chinese_remainder_theorem_entail_wit_1 : chinese_remainder_theorem_entail_wit_1.
Axiom proof_of_chinese_remainder_theorem_entail_wit_2 : chinese_remainder_theorem_entail_wit_2.
Axiom proof_of_chinese_remainder_theorem_entail_wit_3 : chinese_remainder_theorem_entail_wit_3.
Axiom proof_of_chinese_remainder_theorem_entail_wit_4_1 : chinese_remainder_theorem_entail_wit_4_1.
Axiom proof_of_chinese_remainder_theorem_entail_wit_4_2 : chinese_remainder_theorem_entail_wit_4_2.
Axiom proof_of_chinese_remainder_theorem_return_wit_1 : chinese_remainder_theorem_return_wit_1.
Axiom proof_of_chinese_remainder_theorem_partial_solve_wit_1 : chinese_remainder_theorem_partial_solve_wit_1.
Axiom proof_of_chinese_remainder_theorem_partial_solve_wit_2 : chinese_remainder_theorem_partial_solve_wit_2.
Axiom proof_of_chinese_remainder_theorem_partial_solve_wit_3 : chinese_remainder_theorem_partial_solve_wit_3.
Axiom proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure : chinese_remainder_theorem_partial_solve_wit_4_pure.
Axiom proof_of_chinese_remainder_theorem_partial_solve_wit_4 : chinese_remainder_theorem_partial_solve_wit_4.
Axiom proof_of_chinese_remainder_theorem_partial_solve_wit_5 : chinese_remainder_theorem_partial_solve_wit_5.

End VC_Correct.
