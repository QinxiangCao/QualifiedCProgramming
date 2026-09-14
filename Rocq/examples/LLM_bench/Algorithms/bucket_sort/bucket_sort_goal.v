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
Require Import SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_lib.
Local Open Scope sac.

(*----- Function sort -----*)

Definition sort_safety_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth (i) (input) (0))) /\ ((Znth (i) (input) (0)) <= 999999999)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_safety_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre > 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth (i) (input) (0))) /\ ((Znth (i) (input) (0)) <= 999999999)))) ,
  ((( &( "max_value" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_safety_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre > 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth (i) (input) (0))) /\ ((Znth (i) (input) (0)) <= 999999999)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full a_pre n_pre input )
  **  ((( &( "max_value" ) )) # Int  |-> (Znth 0 input 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_safety_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : ((Znth i input 0) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH11 : (PrefixMaximum input i max_value )) ,
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max_value" ) )) # Int  |-> (Znth i input 0))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sort_safety_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : ((Znth i input 0) <= max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH11 : (PrefixMaximum input i max_value )) ,
  (IntArray.full a_pre n_pre input )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sort_safety_wit_6 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH10 : (PrefixMaximum input i max_value )) ,
  ((( &( "exponent" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  (IntArray.full a_pre n_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_safety_wit_7 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (current: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 1000000000)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH11 : (PrefixMaximum input n_pre max_value )) (PreH12 : (DecimalExponent exponent )) (PreH13 : (RadixPassState input current exponent )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
|--
  “ ((max_value <> (INT_MIN)) \/ (exponent <> (-1))) ” 
  &&  “ (exponent <> 0) ”
.

Definition sort_safety_wit_8 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (current: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 1000000000)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH11 : (PrefixMaximum input n_pre max_value )) (PreH12 : (DecimalExponent exponent )) (PreH13 : (RadixPassState input current exponent )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_safety_wit_9 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (current: (@list Z)) (PreH1 : ((max_value ÷ exponent ) > 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value )) (PreH13 : (DecimalExponent exponent )) (PreH14 : (RadixPassState input current exponent )) ,
  ((( &( "digit" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_safety_wit_10 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (digit: Z) (zero_prefix: (@list Z)) (current: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((Zlength (zero_prefix)) = digit)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 100000000)) (PreH10 : (0 < (max_value ÷ exponent ))) (PreH11 : (0 <= digit)) (PreH12 : (digit <= 10)) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < digit)) -> ((Znth (k_3) (zero_prefix) (0)) = 0))) (PreH16 : (PrefixMaximum input n_pre max_value )) (PreH17 : (DecimalExponent exponent )) (PreH18 : (RadixPassState input current exponent )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.seg ( &( "count" ) ) 0 digit zero_prefix )
  **  (IntArray.undef_seg ( &( "count" ) ) digit 10 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition sort_safety_wit_11 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (digit: Z) (zero_prefix: (@list Z)) (current: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (zero_prefix)) = digit)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : (0 <= digit)) (PreH13 : (digit <= 10)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < digit)) -> ((Znth (k_3) (zero_prefix) (0)) = 0))) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current exponent )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.seg ( &( "count" ) ) 0 digit zero_prefix )
  **  (IntArray.undef_seg ( &( "count" ) ) digit 10 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_safety_wit_12 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (digit: Z) (zero_prefix: (@list Z)) (current: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (zero_prefix)) = digit)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : (0 <= digit)) (PreH13 : (digit <= 10)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < digit)) -> ((Znth (k_3) (zero_prefix) (0)) = 0))) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current exponent )) ,
  (IntArray.seg ( &( "count" ) ) 0 (digit + 1 ) (app (zero_prefix) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "count" ) ) (digit + 1 ) 10 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ ((digit + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (digit + 1 )) ”
.

Definition sort_safety_wit_13 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current: (@list Z)) (counts: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((Zlength (counts)) = 10)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 100000000)) (PreH10 : (0 < (max_value ÷ exponent ))) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH13 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((Znth (digit) (counts) (0)) = 0))) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current exponent )) (PreH17 : (DigitHistogramPrefix current exponent 0 counts )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_safety_wit_14 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH16 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current exponent )) (PreH20 : (DigitHistogramPrefix current exponent i counts )) ,
  (IntArray.full a_pre n_pre current )
  **  ((( &( "digit" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ ((((Znth i current 0) ÷ exponent ) <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition sort_safety_wit_15 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH16 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current exponent )) (PreH20 : (DigitHistogramPrefix current exponent i counts )) ,
  (IntArray.full a_pre n_pre current )
  **  ((( &( "digit" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (((Znth i current 0) <> (INT_MIN)) \/ (exponent <> (-1))) ” 
  &&  “ (exponent <> 0) ”
.

Definition sort_safety_wit_16 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH16 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current exponent )) (PreH20 : (DigitHistogramPrefix current exponent i counts )) ,
  (IntArray.full a_pre n_pre current )
  **  ((( &( "digit" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition sort_safety_wit_17 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current: (@list Z)) (PreH1 : (0 <= (((Znth i current 0) ÷ exponent ) % ( 10 ) ))) (PreH2 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (counts)) = 10)) (PreH17 : (0 <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : (0 < (max_value ÷ exponent ))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH26 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value )) (PreH28 : (DecimalExponent exponent )) (PreH29 : (RadixPassState input current exponent )) (PreH30 : (DigitHistogramPrefix current exponent i counts )) ,
  (IntArray.full ( &( "count" ) ) 10 counts )
  **  ((( &( "digit" ) )) # Int  |-> (((Znth i current 0) ÷ exponent ) % ( 10 ) ))
  **  (IntArray.full a_pre n_pre current )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (((Znth (((Znth i current 0) ÷ exponent ) % ( 10 ) ) counts 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (((Znth i current 0) ÷ exponent ) % ( 10 ) ) counts 0) + 1 )) ”
) \/
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current: (@list Z)) (PreH1 : (0 <= (((Znth i current 0) ÷ exponent ) % ( 10 ) ))) (PreH2 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (counts)) = 10)) (PreH17 : (0 <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : (0 < (max_value ÷ exponent ))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH26 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value )) (PreH28 : (DecimalExponent exponent )) (PreH29 : (RadixPassState input current exponent )) (PreH30 : (DigitHistogramPrefix current exponent i counts )) ,
  (IntArray.full ( &( "count" ) ) 10 counts )
  **  ((( &( "digit" ) )) # Int  |-> (((Znth i current 0) ÷ exponent ) % ( 10 ) ))
  **  (IntArray.full a_pre n_pre current )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (((Znth (((Znth i current 0) ÷ exponent ) % ( 10 ) ) counts 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (((Znth i current 0) ÷ exponent ) % ( 10 ) ) counts 0) + 1 )) ”
).

Definition sort_safety_wit_17_split_goal_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current: (@list Z)) (PreH1 : (0 <= (((Znth i current 0) ÷ exponent ) % ( 10 ) ))) (PreH2 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (counts)) = 10)) (PreH17 : (0 <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : (0 < (max_value ÷ exponent ))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH26 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value )) (PreH28 : (DecimalExponent exponent )) (PreH29 : (RadixPassState input current exponent )) (PreH30 : (DigitHistogramPrefix current exponent i counts )) ,
  (IntArray.full ( &( "count" ) ) 10 counts )
  **  ((( &( "digit" ) )) # Int  |-> (((Znth i current 0) ÷ exponent ) % ( 10 ) ))
  **  (IntArray.full a_pre n_pre current )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (((Znth (((Znth i current 0) ÷ exponent ) % ( 10 ) ) counts 0) + 1 ) <= INT_MAX) ”
.

Definition sort_safety_wit_17_split_goal_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current: (@list Z)) (PreH1 : (0 <= (((Znth i current 0) ÷ exponent ) % ( 10 ) ))) (PreH2 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (counts)) = 10)) (PreH17 : (0 <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : (0 < (max_value ÷ exponent ))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH26 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value )) (PreH28 : (DecimalExponent exponent )) (PreH29 : (RadixPassState input current exponent )) (PreH30 : (DigitHistogramPrefix current exponent i counts )) ,
  (IntArray.full ( &( "count" ) ) 10 counts )
  **  ((( &( "digit" ) )) # Int  |-> (((Znth i current 0) ÷ exponent ) % ( 10 ) ))
  **  (IntArray.full a_pre n_pre current )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ ((INT_MIN) <= ((Znth (((Znth i current 0) ÷ exponent ) % ( 10 ) ) counts 0) + 1 )) ”
.

Definition sort_safety_wit_18 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current: (@list Z)) (PreH1 : (0 <= (((Znth i current 0) ÷ exponent ) % ( 10 ) ))) (PreH2 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (counts)) = 10)) (PreH17 : (0 <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : (0 < (max_value ÷ exponent ))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH26 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value )) (PreH28 : (DecimalExponent exponent )) (PreH29 : (RadixPassState input current exponent )) (PreH30 : (DigitHistogramPrefix current exponent i counts )) ,
  (IntArray.full ( &( "count" ) ) 10 (replace_Znth ((((Znth i current 0) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth i current 0) ÷ exponent ) % ( 10 ) ) counts 0) + 1 )) (counts)) )
  **  (IntArray.full a_pre n_pre current )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sort_safety_wit_19 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current: (@list Z)) (histogram: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((Zlength (histogram)) = 10)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 100000000)) (PreH10 : (0 < (max_value ÷ exponent ))) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH13 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)))) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current exponent )) (PreH17 : (DigitHistogramPrefix current exponent n_pre histogram )) ,
  ((( &( "digit" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 histogram )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_safety_wit_20 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (totals: (@list Z)) (histogram: (@list Z)) (current: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((Zlength (histogram)) = 10)) (PreH6 : ((Zlength (totals)) = 10)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : (1 <= digit)) (PreH13 : (digit <= 10)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 10)) -> ((0 <= (Znth (k_3) (histogram) (0))) /\ ((Znth (k_3) (histogram) (0)) <= n_pre)))) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 10)) -> ((0 <= (Znth (k_4) (totals) (0))) /\ ((Znth (k_4) (totals) (0)) <= n_pre)))) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH22 : (DigitPrefixTotals histogram totals digit )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 totals )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition sort_safety_wit_21 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (totals: (@list Z)) (histogram: (@list Z)) (current: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : (0 < (max_value ÷ exponent ))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 10)) -> ((0 <= (Znth (k_3) (histogram) (0))) /\ ((Znth (k_3) (histogram) (0)) <= n_pre)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 10)) -> ((0 <= (Znth (k_4) (totals) (0))) /\ ((Znth (k_4) (totals) (0)) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value )) (PreH20 : (DecimalExponent exponent )) (PreH21 : (RadixPassState input current exponent )) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH23 : (DigitPrefixTotals histogram totals digit )) ,
  (IntArray.full ( &( "count" ) ) 10 totals )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (((Znth digit totals 0) + (Znth (digit - 1 ) totals 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth digit totals 0) + (Znth (digit - 1 ) totals 0) )) ”
) \/
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (totals: (@list Z)) (histogram: (@list Z)) (current: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : (0 < (max_value ÷ exponent ))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 10)) -> ((0 <= (Znth (k_3) (histogram) (0))) /\ ((Znth (k_3) (histogram) (0)) <= n_pre)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 10)) -> ((0 <= (Znth (k_4) (totals) (0))) /\ ((Znth (k_4) (totals) (0)) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value )) (PreH20 : (DecimalExponent exponent )) (PreH21 : (RadixPassState input current exponent )) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH23 : (DigitPrefixTotals histogram totals digit )) ,
  (IntArray.full ( &( "count" ) ) 10 totals )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (((Znth digit totals 0) + (Znth (digit - 1 ) totals 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth digit totals 0) + (Znth (digit - 1 ) totals 0) )) ”
).

Definition sort_safety_wit_21_split_goal_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (totals: (@list Z)) (histogram: (@list Z)) (current: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : (0 < (max_value ÷ exponent ))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 10)) -> ((0 <= (Znth (k_3) (histogram) (0))) /\ ((Znth (k_3) (histogram) (0)) <= n_pre)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 10)) -> ((0 <= (Znth (k_4) (totals) (0))) /\ ((Znth (k_4) (totals) (0)) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value )) (PreH20 : (DecimalExponent exponent )) (PreH21 : (RadixPassState input current exponent )) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH23 : (DigitPrefixTotals histogram totals digit )) ,
  (IntArray.full ( &( "count" ) ) 10 totals )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (((Znth digit totals 0) + (Znth (digit - 1 ) totals 0) ) <= INT_MAX) ”
.

Definition sort_safety_wit_21_split_goal_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (totals: (@list Z)) (histogram: (@list Z)) (current: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : (0 < (max_value ÷ exponent ))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 10)) -> ((0 <= (Znth (k_3) (histogram) (0))) /\ ((Znth (k_3) (histogram) (0)) <= n_pre)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 10)) -> ((0 <= (Znth (k_4) (totals) (0))) /\ ((Znth (k_4) (totals) (0)) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value )) (PreH20 : (DecimalExponent exponent )) (PreH21 : (RadixPassState input current exponent )) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH23 : (DigitPrefixTotals histogram totals digit )) ,
  (IntArray.full ( &( "count" ) ) 10 totals )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ ((INT_MIN) <= ((Znth digit totals 0) + (Znth (digit - 1 ) totals 0) )) ”
.

Definition sort_safety_wit_22 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (totals: (@list Z)) (histogram: (@list Z)) (current: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : (0 < (max_value ÷ exponent ))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 10)) -> ((0 <= (Znth (k_3) (histogram) (0))) /\ ((Znth (k_3) (histogram) (0)) <= n_pre)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 10)) -> ((0 <= (Znth (k_4) (totals) (0))) /\ ((Znth (k_4) (totals) (0)) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value )) (PreH20 : (DecimalExponent exponent )) (PreH21 : (RadixPassState input current exponent )) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH23 : (DigitPrefixTotals histogram totals digit )) ,
  (IntArray.full ( &( "count" ) ) 10 totals )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ ((digit - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (digit - 1 )) ”
.

Definition sort_safety_wit_23 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (totals: (@list Z)) (histogram: (@list Z)) (current: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : (0 < (max_value ÷ exponent ))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 10)) -> ((0 <= (Znth (k_3) (histogram) (0))) /\ ((Znth (k_3) (histogram) (0)) <= n_pre)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 10)) -> ((0 <= (Znth (k_4) (totals) (0))) /\ ((Znth (k_4) (totals) (0)) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value )) (PreH20 : (DecimalExponent exponent )) (PreH21 : (RadixPassState input current exponent )) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH23 : (DigitPrefixTotals histogram totals digit )) ,
  (IntArray.full ( &( "count" ) ) 10 totals )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_safety_wit_24 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (totals: (@list Z)) (histogram: (@list Z)) (current: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : (0 < (max_value ÷ exponent ))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 10)) -> ((0 <= (Znth (k_3) (histogram) (0))) /\ ((Znth (k_3) (histogram) (0)) <= n_pre)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 10)) -> ((0 <= (Znth (k_4) (totals) (0))) /\ ((Znth (k_4) (totals) (0)) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value )) (PreH20 : (DecimalExponent exponent )) (PreH21 : (RadixPassState input current exponent )) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH23 : (DigitPrefixTotals histogram totals digit )) ,
  (IntArray.full ( &( "count" ) ) 10 (replace_Znth (digit) (((Znth digit totals 0) + (Znth (digit - 1 ) totals 0) )) (totals)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "digit" ) )) # Int  |-> digit)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ ((digit + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (digit + 1 )) ”
.

Definition sort_safety_wit_25 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current: (@list Z)) (histogram: (@list Z)) (endpoints: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((Zlength (histogram)) = 10)) (PreH6 : ((Zlength (endpoints)) = 10)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH14 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (endpoints) (0)))) /\ ((Znth (digit) (endpoints) (0)) <= n_pre)))) (PreH15 : (PrefixMaximum input n_pre max_value )) (PreH16 : (DecimalExponent exponent )) (PreH17 : (RadixPassState input current exponent )) (PreH18 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH19 : (DigitPrefixTotals histogram endpoints 10 )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 endpoints )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition sort_safety_wit_26 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current: (@list Z)) (histogram: (@list Z)) (endpoints: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((Zlength (histogram)) = 10)) (PreH6 : ((Zlength (endpoints)) = 10)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH14 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (endpoints) (0)))) /\ ((Znth (digit) (endpoints) (0)) <= n_pre)))) (PreH15 : (PrefixMaximum input n_pre max_value )) (PreH16 : (DecimalExponent exponent )) (PreH17 : (RadixPassState input current exponent )) (PreH18 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH19 : (DigitPrefixTotals histogram endpoints 10 )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 endpoints )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_safety_wit_27 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (counters: (@list Z)) (histogram: (@list Z)) (current: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((Zlength (histogram)) = 10)) (PreH6 : ((Zlength (counters)) = 10)) (PreH7 : ((Zlength (mixed_output)) = 1000)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : (0 < (max_value ÷ exponent ))) (PreH13 : ((-1) <= i)) (PreH14 : (i < n_pre)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH17 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH18 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value )) (PreH20 : (DecimalExponent exponent )) (PreH21 : (RadixPassState input current exponent )) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH23 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_safety_wit_28 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (counters)) = 10)) (PreH8 : ((Zlength (mixed_output)) = 1000)) (PreH9 : (0 <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : (0 < (max_value ÷ exponent ))) (PreH14 : ((-1) <= i)) (PreH15 : (i < n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH18 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH19 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH20 : (PrefixMaximum input n_pre max_value )) (PreH21 : (DecimalExponent exponent )) (PreH22 : (RadixPassState input current exponent )) (PreH23 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH24 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  (IntArray.full a_pre n_pre current )
  **  ((( &( "digit" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ ((((Znth i current 0) ÷ exponent ) <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition sort_safety_wit_29 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (counters)) = 10)) (PreH8 : ((Zlength (mixed_output)) = 1000)) (PreH9 : (0 <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : (0 < (max_value ÷ exponent ))) (PreH14 : ((-1) <= i)) (PreH15 : (i < n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH18 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH19 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH20 : (PrefixMaximum input n_pre max_value )) (PreH21 : (DecimalExponent exponent )) (PreH22 : (RadixPassState input current exponent )) (PreH23 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH24 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  (IntArray.full a_pre n_pre current )
  **  ((( &( "digit" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ (((Znth i current 0) <> (INT_MIN)) \/ (exponent <> (-1))) ” 
  &&  “ (exponent <> 0) ”
.

Definition sort_safety_wit_30 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (counters)) = 10)) (PreH8 : ((Zlength (mixed_output)) = 1000)) (PreH9 : (0 <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : (0 < (max_value ÷ exponent ))) (PreH14 : ((-1) <= i)) (PreH15 : (i < n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH18 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH19 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH20 : (PrefixMaximum input n_pre max_value )) (PreH21 : (DecimalExponent exponent )) (PreH22 : (RadixPassState input current exponent )) (PreH23 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH24 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  (IntArray.full a_pre n_pre current )
  **  ((( &( "digit" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition sort_safety_wit_31 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (0 <= (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH2 : ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)) (PreH3 : (1 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)))) (PreH4 : ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (max_value >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 1000)) (PreH12 : ((Zlength (input)) = n_pre)) (PreH13 : ((Zlength (current)) = n_pre)) (PreH14 : ((Zlength (histogram)) = 10)) (PreH15 : ((Zlength (counters)) = 10)) (PreH16 : ((Zlength (mixed_output)) = 1000)) (PreH17 : (0 <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : (0 < (max_value ÷ exponent ))) (PreH22 : ((-1) <= i)) (PreH23 : (i < n_pre)) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH26 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH27 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH28 : (PrefixMaximum input n_pre max_value )) (PreH29 : (DecimalExponent exponent )) (PreH30 : (RadixPassState input current exponent )) (PreH31 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH32 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  (IntArray.full ( &( "count" ) ) 10 counters )
  **  ((( &( "digit" ) )) # Int  |-> (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ (((Znth (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) counters 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) counters 0) - 1 )) ”
.

Definition sort_safety_wit_32 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (0 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) - 1 )) (counters))) (0)))) (PreH2 : ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) - 1 )) (counters))) (0)) < 1000)) (PreH3 : (exponent <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (exponent >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (0 <= (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH8 : ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)) (PreH9 : (1 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)))) (PreH10 : ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)) (PreH11 : (max_value <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (max_value >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (i >= 0)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : ((Zlength (input)) = n_pre)) (PreH19 : ((Zlength (current)) = n_pre)) (PreH20 : ((Zlength (histogram)) = 10)) (PreH21 : ((Zlength (counters)) = 10)) (PreH22 : ((Zlength (mixed_output)) = 1000)) (PreH23 : (0 <= max_value)) (PreH24 : (max_value <= 999999999)) (PreH25 : (1 <= exponent)) (PreH26 : (exponent <= 100000000)) (PreH27 : (0 < (max_value ÷ exponent ))) (PreH28 : ((-1) <= i)) (PreH29 : (i < n_pre)) (PreH30 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH31 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH32 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH34 : (PrefixMaximum input n_pre max_value )) (PreH35 : (DecimalExponent exponent )) (PreH36 : (RadixPassState input current exponent )) (PreH37 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH38 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  (IntArray.mixed_full ( &( "output" ) ) 1000 (replace_Znth ((Znth (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) (replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) counters 0) - 1 )) (counters)) 0)) ((Some ((Znth i current 0)))) (mixed_output)) )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 (replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) counters 0) - 1 )) (counters)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition sort_safety_wit_33 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current: (@list Z)) (histogram: (@list Z)) (bucket_starts: (@list Z)) (pass_output: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current)) = n_pre)) (PreH5 : ((Zlength (histogram)) = 10)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output)) = n_pre)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : (0 < (max_value ÷ exponent ))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (pass_output) (0)))) /\ ((Znth (k_2) (pass_output) (0)) <= 999999999)))) (PreH15 : (PrefixMaximum input n_pre max_value )) (PreH16 : (DecimalExponent exponent )) (PreH17 : (RadixPassState input current exponent )) (PreH18 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH19 : (StableDigitPass current pass_output exponent )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_safety_wit_34 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (working: (@list Z)) (pass_output: (@list Z)) (bucket_starts: (@list Z)) (current: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output)) = n_pre)) (PreH8 : ((Zlength (working)) = n_pre)) (PreH9 : (0 <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : (0 < (max_value ÷ exponent ))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (pass_output) (0)))) /\ ((Znth (k_2) (pass_output) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (working) (0)))) /\ ((Znth (k_2) (working) (0)) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (StableDigitPass current pass_output exponent )) (PreH22 : (RadixCopyPrefix current pass_output working i )) ,
  (IntArray.full a_pre n_pre (replace_Znth (i) ((Znth (i - 0 ) pass_output 0)) (working)) )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sort_safety_wit_35 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (pass_output: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (pass_output)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (1 <= (exponent * 10 ))) (PreH10 : ((exponent * 10 ) <= 1000000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (pass_output) (0))) /\ ((Znth (k_2) (pass_output) (0)) <= 999999999)))) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent (exponent * 10 ) )) (PreH16 : (RadixPassState input pass_output (exponent * 10 ) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre pass_output )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
|--
  “ ((exponent * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (exponent * 10 )) ”
.

Definition sort_safety_wit_36 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (pass_output: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (pass_output)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (1 <= (exponent * 10 ))) (PreH10 : ((exponent * 10 ) <= 1000000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (pass_output) (0))) /\ ((Znth (k_2) (pass_output) (0)) <= 999999999)))) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent (exponent * 10 ) )) (PreH16 : (RadixPassState input pass_output (exponent * 10 ) )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre pass_output )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition sort_entail_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre > 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth (i) (input) (0))) /\ ((Znth (i) (input) (0)) <= 999999999)))) ,
  (IntArray.full a_pre n_pre input )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= (Znth 0 input 0)) ” 
  &&  “ ((Znth 0 input 0) <= 999999999) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ (PrefixMaximum input 1 (Znth 0 input 0) ) ”
  &&  (IntArray.full a_pre n_pre input )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre > 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth (i) (input) (0))) /\ ((Znth (i) (input) (0)) <= 999999999)))) ,
  TT && emp 
|--
  “ (PrefixMaximum input 1 (Znth 0 input 0) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ ((Znth 0 input 0) <= 999999999) ” 
  &&  “ (0 <= (Znth 0 input 0)) ”
  &&  emp
).

Definition sort_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre > 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth (i) (input) (0))) /\ ((Znth (i) (input) (0)) <= 999999999)))) ,
  (PrefixMaximum input 1 (Znth 0 input 0) )
.

Definition sort_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre > 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth (i) (input) (0))) /\ ((Znth (i) (input) (0)) <= 999999999)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))
.

Definition sort_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre > 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth (i) (input) (0))) /\ ((Znth (i) (input) (0)) <= 999999999)))) ,
  ((Znth 0 input 0) <= 999999999)
.

Definition sort_entail_wit_1_split_goal_4 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre > 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth (i) (input) (0))) /\ ((Znth (i) (input) (0)) <= 999999999)))) ,
  (0 <= (Znth 0 input 0))
.

Definition sort_entail_wit_2_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : ((Znth i input 0) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH11 : (PrefixMaximum input i max_value )) ,
  (IntArray.full a_pre n_pre input )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (Znth i input 0)) ” 
  &&  “ ((Znth i input 0) <= 999999999) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ (PrefixMaximum input (i + 1 ) (Znth i input 0) ) ”
  &&  (IntArray.full a_pre n_pre input )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : ((Znth i input 0) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH11 : (PrefixMaximum input i max_value )) ,
  TT && emp 
|--
  “ (PrefixMaximum input (i + 1 ) (Znth i input 0) ) ” 
  &&  “ ((Znth i input 0) <= 999999999) ”
  &&  emp
).

Definition sort_entail_wit_2_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : ((Znth i input 0) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH11 : (PrefixMaximum input i max_value )) ,
  (PrefixMaximum input (i + 1 ) (Znth i input 0) )
.

Definition sort_entail_wit_2_1_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : ((Znth i input 0) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH11 : (PrefixMaximum input i max_value )) ,
  ((Znth i input 0) <= 999999999)
.

Definition sort_entail_wit_2_2 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : ((Znth i input 0) <= max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH11 : (PrefixMaximum input i max_value )) ,
  (IntArray.full a_pre n_pre input )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ (PrefixMaximum input (i + 1 ) max_value ) ”
  &&  (IntArray.full a_pre n_pre input )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : ((Znth i input 0) <= max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH11 : (PrefixMaximum input i max_value )) ,
  TT && emp 
|--
  “ (PrefixMaximum input (i + 1 ) max_value ) ”
  &&  emp
).

Definition sort_entail_wit_2_2_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : ((Znth i input 0) <= max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH11 : (PrefixMaximum input i max_value )) ,
  (PrefixMaximum input (i + 1 ) max_value )
.

Definition sort_entail_wit_3 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH10 : (PrefixMaximum input i max_value )) ,
  (IntArray.undef_full ( &( "count" ) ) 10 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.full a_pre n_pre input )
|--
  EX (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 1000000000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent 1 ) ” 
  &&  “ (RadixPassState input current 1 ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH10 : (PrefixMaximum input i max_value )) ,
  TT && emp 
|--
  “ (RadixPassState input input 1 ) ” 
  &&  “ (DecimalExponent 1 ) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (input) (0))) /\ ((Znth (k_2) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ”
  &&  emp
).

Definition sort_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH10 : (PrefixMaximum input i max_value )) ,
  (RadixPassState input input 1 )
.

Definition sort_entail_wit_3_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH10 : (PrefixMaximum input i max_value )) ,
  (DecimalExponent 1 )
.

Definition sort_entail_wit_3_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH10 : (PrefixMaximum input i max_value )) ,
  (PrefixMaximum input n_pre max_value )
.

Definition sort_entail_wit_3_split_goal_4 := 
forall (n_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH10 : (PrefixMaximum input i max_value )) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (input) (0))) /\ ((Znth (k_2) (input) (0)) <= 999999999)))
.

Definition sort_entail_wit_3_split_goal_5 := 
forall (n_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH10 : (PrefixMaximum input i max_value )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))
.

Definition sort_entail_wit_4 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (current_2: (@list Z)) (PreH1 : ((max_value ÷ exponent ) > 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (input) (0))) /\ ((Znth (k_4) (input) (0)) <= 999999999)))) (PreH11 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth (k_5) (current_2) (0))) /\ ((Znth (k_5) (current_2) (0)) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value )) (PreH13 : (DecimalExponent exponent )) (PreH14 : (RadixPassState input current_2 exponent )) ,
  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
|--
  EX (zero_prefix: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (zero_prefix)) = 0) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 10) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 0)) -> ((Znth (k_3) (zero_prefix) (0)) = 0)) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.seg ( &( "count" ) ) 0 0 zero_prefix )
  **  (IntArray.undef_seg ( &( "count" ) ) 0 10 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (current_2: (@list Z)) (PreH1 : ((max_value ÷ exponent ) > 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (input) (0))) /\ ((Znth (k_4) (input) (0)) <= 999999999)))) (PreH11 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth (k_5) (current_2) (0))) /\ ((Znth (k_5) (current_2) (0)) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value )) (PreH13 : (DecimalExponent exponent )) (PreH14 : (RadixPassState input current_2 exponent )) ,
  TT && emp 
|--
  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 0)) -> ((Znth (k_3) ((@nil Z)) (0)) = 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition sort_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (current_2: (@list Z)) (PreH1 : ((max_value ÷ exponent ) > 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (input) (0))) /\ ((Znth (k_4) (input) (0)) <= 999999999)))) (PreH11 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth (k_5) (current_2) (0))) /\ ((Znth (k_5) (current_2) (0)) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value )) (PreH13 : (DecimalExponent exponent )) (PreH14 : (RadixPassState input current_2 exponent )) ,
  forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 0)) -> ((Znth (k_3) ((@nil Z)) (0)) = 0))
.

Definition sort_entail_wit_4_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (current_2: (@list Z)) (PreH1 : ((max_value ÷ exponent ) > 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (input) (0))) /\ ((Znth (k_4) (input) (0)) <= 999999999)))) (PreH11 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth (k_5) (current_2) (0))) /\ ((Znth (k_5) (current_2) (0)) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value )) (PreH13 : (DecimalExponent exponent )) (PreH14 : (RadixPassState input current_2 exponent )) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999)))
.

Definition sort_entail_wit_4_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (current_2: (@list Z)) (PreH1 : ((max_value ÷ exponent ) > 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (input) (0))) /\ ((Znth (k_4) (input) (0)) <= 999999999)))) (PreH11 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth (k_5) (current_2) (0))) /\ ((Znth (k_5) (current_2) (0)) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value )) (PreH13 : (DecimalExponent exponent )) (PreH14 : (RadixPassState input current_2 exponent )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))
.

Definition sort_entail_wit_4_split_goal_4 := 
forall (n_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (current_2: (@list Z)) (PreH1 : ((max_value ÷ exponent ) > 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (input) (0))) /\ ((Znth (k_4) (input) (0)) <= 999999999)))) (PreH11 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth (k_5) (current_2) (0))) /\ ((Znth (k_5) (current_2) (0)) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value )) (PreH13 : (DecimalExponent exponent )) (PreH14 : (RadixPassState input current_2 exponent )) ,
  (exponent <= 100000000)
.

Definition sort_entail_wit_4_split_goal_5 := 
forall (n_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (current_2: (@list Z)) (PreH1 : ((max_value ÷ exponent ) > 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (input) (0))) /\ ((Znth (k_4) (input) (0)) <= 999999999)))) (PreH11 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth (k_5) (current_2) (0))) /\ ((Znth (k_5) (current_2) (0)) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value )) (PreH13 : (DecimalExponent exponent )) (PreH14 : (RadixPassState input current_2 exponent )) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition sort_entail_wit_5 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (digit: Z) (zero_prefix_2: (@list Z)) (current_2: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (zero_prefix_2)) = digit)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : (0 <= digit)) (PreH13 : (digit <= 10)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999)))) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < digit)) -> ((Znth (k_3) (zero_prefix_2) (0)) = 0))) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current_2 exponent )) ,
  (IntArray.seg ( &( "count" ) ) 0 (digit + 1 ) (app (zero_prefix_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "count" ) ) (digit + 1 ) 10 )
  **  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  EX (zero_prefix: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (zero_prefix)) = (digit + 1 )) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= (digit + 1 )) ” 
  &&  “ ((digit + 1 ) <= 10) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (digit + 1 ))) -> ((Znth (k_3) (zero_prefix) (0)) = 0)) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.seg ( &( "count" ) ) 0 (digit + 1 ) zero_prefix )
  **  (IntArray.undef_seg ( &( "count" ) ) (digit + 1 ) 10 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (digit: Z) (zero_prefix_2: (@list Z)) (current_2: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (zero_prefix_2)) = digit)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : (0 <= digit)) (PreH13 : (digit <= 10)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999)))) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < digit)) -> ((Znth (k_3) (zero_prefix_2) (0)) = 0))) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current_2 exponent )) ,
  TT && emp 
|--
  “ ((Zlength ((app (zero_prefix_2) ((cons (0) ((@nil Z))))))) = (digit + 1 )) ”
  &&  emp
).

Definition sort_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (digit: Z) (zero_prefix_2: (@list Z)) (current_2: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (zero_prefix_2)) = digit)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : (0 <= digit)) (PreH13 : (digit <= 10)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999)))) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < digit)) -> ((Znth (k_3) (zero_prefix_2) (0)) = 0))) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current_2 exponent )) ,
  ((Zlength ((app (zero_prefix_2) ((cons (0) ((@nil Z))))))) = (digit + 1 ))
.

Definition sort_entail_wit_6 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (digit_2: Z) (zero_prefix: (@list Z)) (current_2: (@list Z)) (PreH1 : (digit_2 >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (zero_prefix)) = digit_2)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : (0 <= digit_2)) (PreH13 : (digit_2 <= 10)) (PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH15 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (current_2) (0))) /\ ((Znth (k_4) (current_2) (0)) <= 999999999)))) (PreH16 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < digit_2)) -> ((Znth (k_5) (zero_prefix) (0)) = 0))) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current_2 exponent )) ,
  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.seg ( &( "count" ) ) 0 digit_2 zero_prefix )
  **  (IntArray.undef_seg ( &( "count" ) ) digit_2 10 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  EX (counts: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((Znth (digit) (counts) (0)) = 0)) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent 0 counts ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (digit_2: Z) (zero_prefix: (@list Z)) (current_2: (@list Z)) (PreH1 : (digit_2 >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (zero_prefix)) = digit_2)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : (0 <= digit_2)) (PreH13 : (digit_2 <= 10)) (PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH15 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (current_2) (0))) /\ ((Znth (k_4) (current_2) (0)) <= 999999999)))) (PreH16 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < digit_2)) -> ((Znth (k_5) (zero_prefix) (0)) = 0))) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current_2 exponent )) ,
  (IntArray.seg ( &( "count" ) ) 0 digit_2 zero_prefix )
|--
  EX (counts: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current_2)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((Znth (digit) (counts) (0)) = 0)) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current_2 exponent ) ” 
  &&  “ (DigitHistogramPrefix current_2 exponent 0 counts ) ”
  &&  (IntArray.full ( &( "count" ) ) 10 counts )
).

Definition sort_entail_wit_7 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (counts_2: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (counts_2)) = 10)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 100000000)) (PreH10 : (0 < (max_value ÷ exponent ))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (current_2) (0))) /\ ((Znth (k_4) (current_2) (0)) <= 999999999)))) (PreH13 : forall (digit_2: Z) , (((0 <= digit_2) /\ (digit_2 < 10)) -> ((Znth (digit_2) (counts_2) (0)) = 0))) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current_2 exponent )) (PreH17 : (DigitHistogramPrefix current_2 exponent 0 counts_2 )) ,
  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.full ( &( "count" ) ) 10 counts_2 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  EX (counts: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= 0))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent 0 counts ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (counts_2: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (counts_2)) = 10)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 100000000)) (PreH10 : (0 < (max_value ÷ exponent ))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (current_2) (0))) /\ ((Znth (k_4) (current_2) (0)) <= 999999999)))) (PreH13 : forall (digit_2: Z) , (((0 <= digit_2) /\ (digit_2 < 10)) -> ((Znth (digit_2) (counts_2) (0)) = 0))) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current_2 exponent )) (PreH17 : (DigitHistogramPrefix current_2 exponent 0 counts_2 )) ,
  TT && emp 
|--
  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts_2) (0))) /\ ((Znth (digit) (counts_2) (0)) <= 0))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ”
  &&  emp
).

Definition sort_entail_wit_7_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (counts_2: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (counts_2)) = 10)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 100000000)) (PreH10 : (0 < (max_value ÷ exponent ))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (current_2) (0))) /\ ((Znth (k_4) (current_2) (0)) <= 999999999)))) (PreH13 : forall (digit_2: Z) , (((0 <= digit_2) /\ (digit_2 < 10)) -> ((Znth (digit_2) (counts_2) (0)) = 0))) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current_2 exponent )) (PreH17 : (DigitHistogramPrefix current_2 exponent 0 counts_2 )) ,
  forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts_2) (0))) /\ ((Znth (digit) (counts_2) (0)) <= 0)))
.

Definition sort_entail_wit_7_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (counts_2: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (counts_2)) = 10)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 100000000)) (PreH10 : (0 < (max_value ÷ exponent ))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (current_2) (0))) /\ ((Znth (k_4) (current_2) (0)) <= 999999999)))) (PreH13 : forall (digit_2: Z) , (((0 <= digit_2) /\ (digit_2 < 10)) -> ((Znth (digit_2) (counts_2) (0)) = 0))) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current_2 exponent )) (PreH17 : (DigitHistogramPrefix current_2 exponent 0 counts_2 )) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999)))
.

Definition sort_entail_wit_7_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (counts_2: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (counts_2)) = 10)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 100000000)) (PreH10 : (0 < (max_value ÷ exponent ))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (current_2) (0))) /\ ((Znth (k_4) (current_2) (0)) <= 999999999)))) (PreH13 : forall (digit_2: Z) , (((0 <= digit_2) /\ (digit_2 < 10)) -> ((Znth (digit_2) (counts_2) (0)) = 0))) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current_2 exponent )) (PreH17 : (DigitHistogramPrefix current_2 exponent 0 counts_2 )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))
.

Definition sort_entail_wit_8 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH16 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current exponent )) (PreH20 : (DigitHistogramPrefix current exponent i counts )) ,
  (IntArray.full a_pre n_pre current )
  **  ((( &( "digit" ) )) # Int  |-> (((Znth i current 0) ÷ exponent ) % ( 10 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (0 <= (((Znth i current 0) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) < 10) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (exponent <= INT_MAX) ” 
  &&  “ (max_value <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (exponent >= INT_MIN) ” 
  &&  “ (max_value >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= i))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent i counts ) ”
  &&  ((( &( "digit" ) )) # Int  |-> (((Znth i current 0) ÷ exponent ) % ( 10 ) ))
  **  (IntArray.full a_pre n_pre current )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current: (@list Z)) (PreH1 : (i <= INT_MAX)) (PreH2 : (exponent <= INT_MAX)) (PreH3 : (max_value <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (exponent >= INT_MIN)) (PreH8 : (max_value >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (counts)) = 10)) (PreH17 : (0 <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : (0 < (max_value ÷ exponent ))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH26 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value )) (PreH28 : (DecimalExponent exponent )) (PreH29 : (RadixPassState input current exponent )) (PreH30 : (DigitHistogramPrefix current exponent i counts )) ,
  TT && emp 
|--
  “ ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) < 10) ” 
  &&  “ (0 <= (((Znth i current 0) ÷ exponent ) % ( 10 ) )) ”
  &&  emp
).

Definition sort_entail_wit_8_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current: (@list Z)) (PreH1 : (i <= INT_MAX)) (PreH2 : (exponent <= INT_MAX)) (PreH3 : (max_value <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (exponent >= INT_MIN)) (PreH8 : (max_value >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (counts)) = 10)) (PreH17 : (0 <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : (0 < (max_value ÷ exponent ))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH26 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value )) (PreH28 : (DecimalExponent exponent )) (PreH29 : (RadixPassState input current exponent )) (PreH30 : (DigitHistogramPrefix current exponent i counts )) ,
  ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) < 10)
.

Definition sort_entail_wit_8_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current: (@list Z)) (PreH1 : (i <= INT_MAX)) (PreH2 : (exponent <= INT_MAX)) (PreH3 : (max_value <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (exponent >= INT_MIN)) (PreH8 : (max_value >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (counts)) = 10)) (PreH17 : (0 <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : (0 < (max_value ÷ exponent ))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH26 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value )) (PreH28 : (DecimalExponent exponent )) (PreH29 : (RadixPassState input current exponent )) (PreH30 : (DigitHistogramPrefix current exponent i counts )) ,
  (0 <= (((Znth i current 0) ÷ exponent ) % ( 10 ) ))
.

Definition sort_entail_wit_9 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts_2: (@list Z)) (current_2: (@list Z)) (PreH1 : (0 <= (((Znth i current_2 0) ÷ exponent ) % ( 10 ) ))) (PreH2 : ((((Znth i current_2 0) ÷ exponent ) % ( 10 ) ) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current_2)) = n_pre)) (PreH16 : ((Zlength (counts_2)) = 10)) (PreH17 : (0 <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : (0 < (max_value ÷ exponent ))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999)))) (PreH26 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts_2) (0))) /\ ((Znth (digit) (counts_2) (0)) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value )) (PreH28 : (DecimalExponent exponent )) (PreH29 : (RadixPassState input current_2 exponent )) (PreH30 : (DigitHistogramPrefix current_2 exponent i counts_2 )) ,
  (IntArray.full ( &( "count" ) ) 10 (replace_Znth ((((Znth i current_2 0) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth i current_2 0) ÷ exponent ) % ( 10 ) ) counts_2 0) + 1 )) (counts_2)) )
  **  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  EX (counts: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= (i + 1 )))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent (i + 1 ) counts ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts_2: (@list Z)) (current_2: (@list Z)) (PreH1 : (0 <= (((Znth i current_2 0) ÷ exponent ) % ( 10 ) ))) (PreH2 : ((((Znth i current_2 0) ÷ exponent ) % ( 10 ) ) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current_2)) = n_pre)) (PreH16 : ((Zlength (counts_2)) = 10)) (PreH17 : (0 <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : (0 < (max_value ÷ exponent ))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999)))) (PreH26 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts_2) (0))) /\ ((Znth (digit) (counts_2) (0)) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value )) (PreH28 : (DecimalExponent exponent )) (PreH29 : (RadixPassState input current_2 exponent )) (PreH30 : (DigitHistogramPrefix current_2 exponent i counts_2 )) ,
  TT && emp 
|--
  “ (DigitHistogramPrefix current_2 exponent (i + 1 ) (replace_Znth ((((Znth i current_2 0) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth i current_2 0) ÷ exponent ) % ( 10 ) ) counts_2 0) + 1 )) (counts_2)) ) ” 
  &&  “ ((Zlength ((replace_Znth ((((Znth i current_2 0) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth i current_2 0) ÷ exponent ) % ( 10 ) ) counts_2 0) + 1 )) (counts_2)))) = 10) ”
  &&  emp
).

Definition sort_entail_wit_9_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts_2: (@list Z)) (current_2: (@list Z)) (PreH1 : (0 <= (((Znth i current_2 0) ÷ exponent ) % ( 10 ) ))) (PreH2 : ((((Znth i current_2 0) ÷ exponent ) % ( 10 ) ) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current_2)) = n_pre)) (PreH16 : ((Zlength (counts_2)) = 10)) (PreH17 : (0 <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : (0 < (max_value ÷ exponent ))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999)))) (PreH26 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts_2) (0))) /\ ((Znth (digit) (counts_2) (0)) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value )) (PreH28 : (DecimalExponent exponent )) (PreH29 : (RadixPassState input current_2 exponent )) (PreH30 : (DigitHistogramPrefix current_2 exponent i counts_2 )) ,
  (DigitHistogramPrefix current_2 exponent (i + 1 ) (replace_Znth ((((Znth i current_2 0) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth i current_2 0) ÷ exponent ) % ( 10 ) ) counts_2 0) + 1 )) (counts_2)) )
.

Definition sort_entail_wit_9_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts_2: (@list Z)) (current_2: (@list Z)) (PreH1 : (0 <= (((Znth i current_2 0) ÷ exponent ) % ( 10 ) ))) (PreH2 : ((((Znth i current_2 0) ÷ exponent ) % ( 10 ) ) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current_2)) = n_pre)) (PreH16 : ((Zlength (counts_2)) = 10)) (PreH17 : (0 <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : (0 < (max_value ÷ exponent ))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999)))) (PreH26 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts_2) (0))) /\ ((Znth (digit) (counts_2) (0)) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value )) (PreH28 : (DecimalExponent exponent )) (PreH29 : (RadixPassState input current_2 exponent )) (PreH30 : (DigitHistogramPrefix current_2 exponent i counts_2 )) ,
  ((Zlength ((replace_Znth ((((Znth i current_2 0) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth i current_2 0) ÷ exponent ) % ( 10 ) ) counts_2 0) + 1 )) (counts_2)))) = 10)
.

Definition sort_entail_wit_10 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH15 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (current_2) (0))) /\ ((Znth (k_4) (current_2) (0)) <= 999999999)))) (PreH16 : forall (digit_2: Z) , (((0 <= digit_2) /\ (digit_2 < 10)) -> ((0 <= (Znth (digit_2) (counts) (0))) /\ ((Znth (digit_2) (counts) (0)) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current_2 exponent )) (PreH20 : (DigitHistogramPrefix current_2 exponent i counts )) ,
  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  EX (histogram: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 histogram )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH15 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (current_2) (0))) /\ ((Znth (k_4) (current_2) (0)) <= 999999999)))) (PreH16 : forall (digit_2: Z) , (((0 <= digit_2) /\ (digit_2 < 10)) -> ((0 <= (Znth (digit_2) (counts) (0))) /\ ((Znth (digit_2) (counts) (0)) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current_2 exponent )) (PreH20 : (DigitHistogramPrefix current_2 exponent i counts )) ,
  TT && emp 
|--
  “ (DigitHistogramPrefix current_2 exponent n_pre counts ) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ”
  &&  emp
).

Definition sort_entail_wit_10_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH15 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (current_2) (0))) /\ ((Znth (k_4) (current_2) (0)) <= 999999999)))) (PreH16 : forall (digit_2: Z) , (((0 <= digit_2) /\ (digit_2 < 10)) -> ((0 <= (Znth (digit_2) (counts) (0))) /\ ((Znth (digit_2) (counts) (0)) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current_2 exponent )) (PreH20 : (DigitHistogramPrefix current_2 exponent i counts )) ,
  (DigitHistogramPrefix current_2 exponent n_pre counts )
.

Definition sort_entail_wit_10_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH15 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (current_2) (0))) /\ ((Znth (k_4) (current_2) (0)) <= 999999999)))) (PreH16 : forall (digit_2: Z) , (((0 <= digit_2) /\ (digit_2 < 10)) -> ((0 <= (Znth (digit_2) (counts) (0))) /\ ((Znth (digit_2) (counts) (0)) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current_2 exponent )) (PreH20 : (DigitHistogramPrefix current_2 exponent i counts )) ,
  forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= n_pre)))
.

Definition sort_entail_wit_10_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH15 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (current_2) (0))) /\ ((Znth (k_4) (current_2) (0)) <= 999999999)))) (PreH16 : forall (digit_2: Z) , (((0 <= digit_2) /\ (digit_2 < 10)) -> ((0 <= (Znth (digit_2) (counts) (0))) /\ ((Znth (digit_2) (counts) (0)) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current_2 exponent )) (PreH20 : (DigitHistogramPrefix current_2 exponent i counts )) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999)))
.

Definition sort_entail_wit_10_split_goal_4 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH15 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (current_2) (0))) /\ ((Znth (k_4) (current_2) (0)) <= 999999999)))) (PreH16 : forall (digit_2: Z) , (((0 <= digit_2) /\ (digit_2 < 10)) -> ((0 <= (Znth (digit_2) (counts) (0))) /\ ((Znth (digit_2) (counts) (0)) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current_2 exponent )) (PreH20 : (DigitHistogramPrefix current_2 exponent i counts )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))
.

Definition sort_entail_wit_11 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (histogram_2: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (histogram_2)) = 10)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 100000000)) (PreH10 : (0 < (max_value ÷ exponent ))) (PreH11 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth (k_5) (input) (0))) /\ ((Znth (k_5) (input) (0)) <= 999999999)))) (PreH12 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth (k_6) (current_2) (0))) /\ ((Znth (k_6) (current_2) (0)) <= 999999999)))) (PreH13 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (histogram_2) (0))) /\ ((Znth (digit) (histogram_2) (0)) <= n_pre)))) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current_2 exponent )) (PreH17 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2 )) ,
  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.full ( &( "count" ) ) 10 histogram_2 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  EX (totals: (@list Z))  (histogram: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength (totals)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 10) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 10)) -> ((0 <= (Znth (k_3) (histogram) (0))) /\ ((Znth (k_3) (histogram) (0)) <= n_pre))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 10)) -> ((0 <= (Znth (k_4) (totals) (0))) /\ ((Znth (k_4) (totals) (0)) <= n_pre))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (DigitPrefixTotals histogram totals 1 ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 totals )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (histogram_2: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (histogram_2)) = 10)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 100000000)) (PreH10 : (0 < (max_value ÷ exponent ))) (PreH11 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth (k_5) (input) (0))) /\ ((Znth (k_5) (input) (0)) <= 999999999)))) (PreH12 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth (k_6) (current_2) (0))) /\ ((Znth (k_6) (current_2) (0)) <= 999999999)))) (PreH13 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (histogram_2) (0))) /\ ((Znth (digit) (histogram_2) (0)) <= n_pre)))) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent exponent )) (PreH16 : (RadixPassState input current_2 exponent )) (PreH17 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2 )) ,
  TT && emp 
|--
  EX (histogram: (@list Z)) ,
  “ ((Zlength (histogram)) = 10) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 10) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 10)) -> ((0 <= (Znth (k_3) (histogram) (0))) /\ ((Znth (k_3) (histogram) (0)) <= (Zlength (input))))) ” 
  &&  “ (DigitHistogramPrefix current_2 exponent (Zlength (input)) histogram ) ” 
  &&  “ (DigitPrefixTotals histogram histogram_2 1 ) ”
  &&  emp
).

Definition sort_entail_wit_12 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (totals_2: (@list Z)) (histogram_2: (@list Z)) (current_2: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (histogram_2)) = 10)) (PreH7 : ((Zlength (totals_2)) = 10)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : (0 < (max_value ÷ exponent ))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 10)) -> ((0 <= (Znth (k_3) (histogram_2) (0))) /\ ((Znth (k_3) (histogram_2) (0)) <= n_pre)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 10)) -> ((0 <= (Znth (k_4) (totals_2) (0))) /\ ((Znth (k_4) (totals_2) (0)) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value )) (PreH20 : (DecimalExponent exponent )) (PreH21 : (RadixPassState input current_2 exponent )) (PreH22 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2 )) (PreH23 : (DigitPrefixTotals histogram_2 totals_2 digit )) ,
  (IntArray.full ( &( "count" ) ) 10 (replace_Znth (digit) (((Znth digit totals_2 0) + (Znth (digit - 1 ) totals_2 0) )) (totals_2)) )
  **  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  EX (totals: (@list Z))  (histogram: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength (totals)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (1 <= (digit + 1 )) ” 
  &&  “ ((digit + 1 ) <= 10) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 10)) -> ((0 <= (Znth (k_3) (histogram) (0))) /\ ((Znth (k_3) (histogram) (0)) <= n_pre))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 10)) -> ((0 <= (Znth (k_4) (totals) (0))) /\ ((Znth (k_4) (totals) (0)) <= n_pre))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (DigitPrefixTotals histogram totals (digit + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 totals )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (totals_2: (@list Z)) (histogram_2: (@list Z)) (current_2: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (histogram_2)) = 10)) (PreH7 : ((Zlength (totals_2)) = 10)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : (0 < (max_value ÷ exponent ))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 10)) -> ((0 <= (Znth (k_3) (histogram_2) (0))) /\ ((Znth (k_3) (histogram_2) (0)) <= n_pre)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 10)) -> ((0 <= (Znth (k_4) (totals_2) (0))) /\ ((Znth (k_4) (totals_2) (0)) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value )) (PreH20 : (DecimalExponent exponent )) (PreH21 : (RadixPassState input current_2 exponent )) (PreH22 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2 )) (PreH23 : (DigitPrefixTotals histogram_2 totals_2 digit )) ,
  TT && emp 
|--
  EX (histogram: (@list Z)) ,
  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength ((replace_Znth (digit) (((Znth digit totals_2 0) + (Znth (digit - 1 ) totals_2 0) )) (totals_2)))) = 10) ” 
  &&  “ (1 <= (digit + 1 )) ” 
  &&  “ ((digit + 1 ) <= 10) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 10)) -> ((0 <= (Znth (k_3) (histogram) (0))) /\ ((Znth (k_3) (histogram) (0)) <= (Zlength (input))))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 10)) -> ((0 <= (Znth (k_4) ((replace_Znth (digit) (((Znth digit totals_2 0) + (Znth (digit - 1 ) totals_2 0) )) (totals_2))) (0))) /\ ((Znth (k_4) ((replace_Znth (digit) (((Znth digit totals_2 0) + (Znth (digit - 1 ) totals_2 0) )) (totals_2))) (0)) <= (Zlength (input))))) ” 
  &&  “ (DigitHistogramPrefix current_2 exponent (Zlength (input)) histogram ) ” 
  &&  “ (DigitPrefixTotals histogram (replace_Znth (digit) (((Znth digit totals_2 0) + (Znth (digit - 1 ) totals_2 0) )) (totals_2)) (digit + 1 ) ) ”
  &&  emp
).

Definition sort_entail_wit_13 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (digit_2: Z) (exponent: Z) (max_value: Z) (totals: (@list Z)) (histogram_2: (@list Z)) (current_2: (@list Z)) (PreH1 : (digit_2 >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (histogram_2)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : (0 < (max_value ÷ exponent ))) (PreH13 : (1 <= digit_2)) (PreH14 : (digit_2 <= 10)) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (current_2) (0))) /\ ((Znth (k_4) (current_2) (0)) <= 999999999)))) (PreH17 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < 10)) -> ((0 <= (Znth (k_5) (histogram_2) (0))) /\ ((Znth (k_5) (histogram_2) (0)) <= n_pre)))) (PreH18 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < 10)) -> ((0 <= (Znth (k_6) (totals) (0))) /\ ((Znth (k_6) (totals) (0)) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value )) (PreH20 : (DecimalExponent exponent )) (PreH21 : (RadixPassState input current_2 exponent )) (PreH22 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2 )) (PreH23 : (DigitPrefixTotals histogram_2 totals digit_2 )) ,
  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.full ( &( "count" ) ) 10 totals )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  EX (endpoints: (@list Z))  (histogram: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength (endpoints)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (endpoints) (0)))) /\ ((Znth (digit) (endpoints) (0)) <= n_pre))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (DigitPrefixTotals histogram endpoints 10 ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 endpoints )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (digit_2: Z) (exponent: Z) (max_value: Z) (totals: (@list Z)) (histogram_2: (@list Z)) (current_2: (@list Z)) (PreH1 : (digit_2 >= 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (histogram_2)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : (0 < (max_value ÷ exponent ))) (PreH13 : (1 <= digit_2)) (PreH14 : (digit_2 <= 10)) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (current_2) (0))) /\ ((Znth (k_4) (current_2) (0)) <= 999999999)))) (PreH17 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < 10)) -> ((0 <= (Znth (k_5) (histogram_2) (0))) /\ ((Znth (k_5) (histogram_2) (0)) <= n_pre)))) (PreH18 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < 10)) -> ((0 <= (Znth (k_6) (totals) (0))) /\ ((Znth (k_6) (totals) (0)) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value )) (PreH20 : (DecimalExponent exponent )) (PreH21 : (RadixPassState input current_2 exponent )) (PreH22 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2 )) (PreH23 : (DigitPrefixTotals histogram_2 totals digit_2 )) ,
  TT && emp 
|--
  EX (histogram: (@list Z)) ,
  “ ((Zlength (histogram)) = 10) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= (Zlength (input)))) /\ (0 <= (Znth (digit) (totals) (0)))) /\ ((Znth (digit) (totals) (0)) <= (Zlength (input))))) ” 
  &&  “ (DigitHistogramPrefix current_2 exponent (Zlength (input)) histogram ) ” 
  &&  “ (DigitPrefixTotals histogram totals 10 ) ”
  &&  emp
).

Definition sort_entail_wit_14 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (histogram_2: (@list Z)) (endpoints: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (histogram_2)) = 10)) (PreH6 : ((Zlength (endpoints)) = 10)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (input) (0))) /\ ((Znth (k_4) (input) (0)) <= 999999999)))) (PreH13 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth (k_5) (current_2) (0))) /\ ((Znth (k_5) (current_2) (0)) <= 999999999)))) (PreH14 : forall (digit_2: Z) , (((0 <= digit_2) /\ (digit_2 < 10)) -> ((((0 <= (Znth (digit_2) (histogram_2) (0))) /\ ((Znth (digit_2) (histogram_2) (0)) <= n_pre)) /\ (0 <= (Znth (digit_2) (endpoints) (0)))) /\ ((Znth (digit_2) (endpoints) (0)) <= n_pre)))) (PreH15 : (PrefixMaximum input n_pre max_value )) (PreH16 : (DecimalExponent exponent )) (PreH17 : (RadixPassState input current_2 exponent )) (PreH18 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2 )) (PreH19 : (DigitPrefixTotals histogram_2 endpoints 10 )) ,
  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.full ( &( "count" ) ) 10 endpoints )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  EX (mixed_output: (@list (@option Z)))  (counters: (@list Z))  (histogram: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength (counters)) = 10) ” 
  &&  “ ((Zlength (mixed_output)) = 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ ((-1) <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= (n_pre - 1 ))) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (BucketPlacementProgress current exponent ((n_pre - 1 ) + 1 ) histogram counters mixed_output ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (histogram_2: (@list Z)) (endpoints: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (histogram_2)) = 10)) (PreH6 : ((Zlength (endpoints)) = 10)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (input) (0))) /\ ((Znth (k_4) (input) (0)) <= 999999999)))) (PreH13 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth (k_5) (current_2) (0))) /\ ((Znth (k_5) (current_2) (0)) <= 999999999)))) (PreH14 : forall (digit_2: Z) , (((0 <= digit_2) /\ (digit_2 < 10)) -> ((((0 <= (Znth (digit_2) (histogram_2) (0))) /\ ((Znth (digit_2) (histogram_2) (0)) <= n_pre)) /\ (0 <= (Znth (digit_2) (endpoints) (0)))) /\ ((Znth (digit_2) (endpoints) (0)) <= n_pre)))) (PreH15 : (PrefixMaximum input n_pre max_value )) (PreH16 : (DecimalExponent exponent )) (PreH17 : (RadixPassState input current_2 exponent )) (PreH18 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2 )) (PreH19 : (DigitPrefixTotals histogram_2 endpoints 10 )) ,
  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  EX (mixed_output: (@list (@option Z)))  (histogram: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current_2)) = n_pre) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength (endpoints)) = 10) ” 
  &&  “ ((Zlength (mixed_output)) = 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ ((-1) <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current_2) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current_2) (0)) ÷ exponent ) % ( 10 ) ) < 10))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (endpoints) (0)))) /\ ((Znth (digit) (endpoints) (0)) <= n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= (n_pre - 1 ))) -> ((1 <= (Znth ((((Znth (k_3) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (endpoints) (0))) /\ ((Znth ((((Znth (k_3) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (endpoints) (0)) <= n_pre))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current_2 exponent ) ” 
  &&  “ (DigitHistogramPrefix current_2 exponent n_pre histogram ) ” 
  &&  “ (BucketPlacementProgress current_2 exponent ((n_pre - 1 ) + 1 ) histogram endpoints mixed_output ) ”
  &&  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
).

Definition sort_entail_wit_15 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (counters)) = 10)) (PreH8 : ((Zlength (mixed_output)) = 1000)) (PreH9 : (0 <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : (0 < (max_value ÷ exponent ))) (PreH14 : ((-1) <= i)) (PreH15 : (i < n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH18 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH19 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH20 : (PrefixMaximum input n_pre max_value )) (PreH21 : (DecimalExponent exponent )) (PreH22 : (RadixPassState input current exponent )) (PreH23 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH24 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  (IntArray.full a_pre n_pre current )
  **  ((( &( "digit" ) )) # Int  |-> (((Znth i current 0) ÷ exponent ) % ( 10 ) ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ (0 <= (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10) ” 
  &&  “ ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) = (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ (1 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) ” 
  &&  “ ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre) ” 
  &&  “ (max_value <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (max_value >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength (counters)) = 10) ” 
  &&  “ ((Zlength (mixed_output)) = 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output ) ”
  &&  ((( &( "digit" ) )) # Int  |-> (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (i <= INT_MAX)) (PreH2 : (exponent <= INT_MAX)) (PreH3 : (max_value <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (exponent >= INT_MIN)) (PreH8 : (max_value >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (histogram)) = 10)) (PreH17 : ((Zlength (counters)) = 10)) (PreH18 : ((Zlength (mixed_output)) = 1000)) (PreH19 : (0 <= max_value)) (PreH20 : (max_value <= 999999999)) (PreH21 : (1 <= exponent)) (PreH22 : (exponent <= 100000000)) (PreH23 : (0 < (max_value ÷ exponent ))) (PreH24 : ((-1) <= i)) (PreH25 : (i < n_pre)) (PreH26 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH27 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH28 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH29 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH30 : (PrefixMaximum input n_pre max_value )) (PreH31 : (DecimalExponent exponent )) (PreH32 : (RadixPassState input current exponent )) (PreH33 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH34 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  TT && emp 
|--
  “ ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre) ” 
  &&  “ (1 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) ” 
  &&  “ ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10) ” 
  &&  “ (0 <= (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ”
  &&  emp
).

Definition sort_entail_wit_15_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (i <= INT_MAX)) (PreH2 : (exponent <= INT_MAX)) (PreH3 : (max_value <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (exponent >= INT_MIN)) (PreH8 : (max_value >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (histogram)) = 10)) (PreH17 : ((Zlength (counters)) = 10)) (PreH18 : ((Zlength (mixed_output)) = 1000)) (PreH19 : (0 <= max_value)) (PreH20 : (max_value <= 999999999)) (PreH21 : (1 <= exponent)) (PreH22 : (exponent <= 100000000)) (PreH23 : (0 < (max_value ÷ exponent ))) (PreH24 : ((-1) <= i)) (PreH25 : (i < n_pre)) (PreH26 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH27 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH28 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH29 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH30 : (PrefixMaximum input n_pre max_value )) (PreH31 : (DecimalExponent exponent )) (PreH32 : (RadixPassState input current exponent )) (PreH33 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH34 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)
.

Definition sort_entail_wit_15_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (i <= INT_MAX)) (PreH2 : (exponent <= INT_MAX)) (PreH3 : (max_value <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (exponent >= INT_MIN)) (PreH8 : (max_value >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (histogram)) = 10)) (PreH17 : ((Zlength (counters)) = 10)) (PreH18 : ((Zlength (mixed_output)) = 1000)) (PreH19 : (0 <= max_value)) (PreH20 : (max_value <= 999999999)) (PreH21 : (1 <= exponent)) (PreH22 : (exponent <= 100000000)) (PreH23 : (0 < (max_value ÷ exponent ))) (PreH24 : ((-1) <= i)) (PreH25 : (i < n_pre)) (PreH26 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH27 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH28 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH29 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH30 : (PrefixMaximum input n_pre max_value )) (PreH31 : (DecimalExponent exponent )) (PreH32 : (RadixPassState input current exponent )) (PreH33 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH34 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  (1 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)))
.

Definition sort_entail_wit_15_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (i <= INT_MAX)) (PreH2 : (exponent <= INT_MAX)) (PreH3 : (max_value <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (exponent >= INT_MIN)) (PreH8 : (max_value >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (histogram)) = 10)) (PreH17 : ((Zlength (counters)) = 10)) (PreH18 : ((Zlength (mixed_output)) = 1000)) (PreH19 : (0 <= max_value)) (PreH20 : (max_value <= 999999999)) (PreH21 : (1 <= exponent)) (PreH22 : (exponent <= 100000000)) (PreH23 : (0 < (max_value ÷ exponent ))) (PreH24 : ((-1) <= i)) (PreH25 : (i < n_pre)) (PreH26 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH27 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH28 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH29 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH30 : (PrefixMaximum input n_pre max_value )) (PreH31 : (DecimalExponent exponent )) (PreH32 : (RadixPassState input current exponent )) (PreH33 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH34 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)
.

Definition sort_entail_wit_15_split_goal_4 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (i <= INT_MAX)) (PreH2 : (exponent <= INT_MAX)) (PreH3 : (max_value <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) <= INT_MAX)) (PreH6 : (i >= INT_MIN)) (PreH7 : (exponent >= INT_MIN)) (PreH8 : (max_value >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) >= INT_MIN)) (PreH11 : (i >= 0)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (histogram)) = 10)) (PreH17 : ((Zlength (counters)) = 10)) (PreH18 : ((Zlength (mixed_output)) = 1000)) (PreH19 : (0 <= max_value)) (PreH20 : (max_value <= 999999999)) (PreH21 : (1 <= exponent)) (PreH22 : (exponent <= 100000000)) (PreH23 : (0 < (max_value ÷ exponent ))) (PreH24 : ((-1) <= i)) (PreH25 : (i < n_pre)) (PreH26 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH27 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH28 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH29 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH30 : (PrefixMaximum input n_pre max_value )) (PreH31 : (DecimalExponent exponent )) (PreH32 : (RadixPassState input current exponent )) (PreH33 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH34 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  (0 <= (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))
.

Definition sort_entail_wit_16 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (0 <= (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH2 : ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)) (PreH3 : (1 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)))) (PreH4 : ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (max_value >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 1000)) (PreH12 : ((Zlength (input)) = n_pre)) (PreH13 : ((Zlength (current)) = n_pre)) (PreH14 : ((Zlength (histogram)) = 10)) (PreH15 : ((Zlength (counters)) = 10)) (PreH16 : ((Zlength (mixed_output)) = 1000)) (PreH17 : (0 <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : (0 < (max_value ÷ exponent ))) (PreH22 : ((-1) <= i)) (PreH23 : (i < n_pre)) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH26 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH27 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH28 : (PrefixMaximum input n_pre max_value )) (PreH29 : (DecimalExponent exponent )) (PreH30 : (RadixPassState input current exponent )) (PreH31 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH32 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  (IntArray.full ( &( "count" ) ) 10 (replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) counters 0) - 1 )) (counters)) )
  **  ((( &( "digit" ) )) # Int  |-> (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ (0 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) - 1 )) (counters))) (0))) ” 
  &&  “ ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) - 1 )) (counters))) (0)) < 1000) ” 
  &&  “ (exponent <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (exponent >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (0 <= (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10) ” 
  &&  “ (1 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) ” 
  &&  “ ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre) ” 
  &&  “ (max_value <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (max_value >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength (counters)) = 10) ” 
  &&  “ ((Zlength (mixed_output)) = 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output ) ”
  &&  ((( &( "digit" ) )) # Int  |-> (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))
  **  (IntArray.full ( &( "count" ) ) 10 (replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) counters 0) - 1 )) (counters)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  (IntArray.full a_pre n_pre current )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (exponent <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) <= INT_MAX)) (PreH4 : (exponent >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) >= INT_MIN)) (PreH7 : (0 <= (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH8 : ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)) (PreH9 : (1 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)))) (PreH10 : ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)) (PreH11 : (max_value <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (max_value >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (i >= 0)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : ((Zlength (input)) = n_pre)) (PreH19 : ((Zlength (current)) = n_pre)) (PreH20 : ((Zlength (histogram)) = 10)) (PreH21 : ((Zlength (counters)) = 10)) (PreH22 : ((Zlength (mixed_output)) = 1000)) (PreH23 : (0 <= max_value)) (PreH24 : (max_value <= 999999999)) (PreH25 : (1 <= exponent)) (PreH26 : (exponent <= 100000000)) (PreH27 : (0 < (max_value ÷ exponent ))) (PreH28 : ((-1) <= i)) (PreH29 : (i < n_pre)) (PreH30 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH31 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH32 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH34 : (PrefixMaximum input n_pre max_value )) (PreH35 : (DecimalExponent exponent )) (PreH36 : (RadixPassState input current exponent )) (PreH37 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH38 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  TT && emp 
|--
  “ ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) - 1 )) (counters))) (0)) < 1000) ” 
  &&  “ (0 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) - 1 )) (counters))) (0))) ”
  &&  emp
).

Definition sort_entail_wit_16_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (exponent <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) <= INT_MAX)) (PreH4 : (exponent >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) >= INT_MIN)) (PreH7 : (0 <= (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH8 : ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)) (PreH9 : (1 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)))) (PreH10 : ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)) (PreH11 : (max_value <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (max_value >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (i >= 0)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : ((Zlength (input)) = n_pre)) (PreH19 : ((Zlength (current)) = n_pre)) (PreH20 : ((Zlength (histogram)) = 10)) (PreH21 : ((Zlength (counters)) = 10)) (PreH22 : ((Zlength (mixed_output)) = 1000)) (PreH23 : (0 <= max_value)) (PreH24 : (max_value <= 999999999)) (PreH25 : (1 <= exponent)) (PreH26 : (exponent <= 100000000)) (PreH27 : (0 < (max_value ÷ exponent ))) (PreH28 : ((-1) <= i)) (PreH29 : (i < n_pre)) (PreH30 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH31 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH32 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH34 : (PrefixMaximum input n_pre max_value )) (PreH35 : (DecimalExponent exponent )) (PreH36 : (RadixPassState input current exponent )) (PreH37 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH38 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) - 1 )) (counters))) (0)) < 1000)
.

Definition sort_entail_wit_16_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (exponent <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) <= INT_MAX)) (PreH4 : (exponent >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) >= INT_MIN)) (PreH7 : (0 <= (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH8 : ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)) (PreH9 : (1 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)))) (PreH10 : ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)) (PreH11 : (max_value <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (max_value >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (i >= 0)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : ((Zlength (input)) = n_pre)) (PreH19 : ((Zlength (current)) = n_pre)) (PreH20 : ((Zlength (histogram)) = 10)) (PreH21 : ((Zlength (counters)) = 10)) (PreH22 : ((Zlength (mixed_output)) = 1000)) (PreH23 : (0 <= max_value)) (PreH24 : (max_value <= 999999999)) (PreH25 : (1 <= exponent)) (PreH26 : (exponent <= 100000000)) (PreH27 : (0 < (max_value ÷ exponent ))) (PreH28 : ((-1) <= i)) (PreH29 : (i < n_pre)) (PreH30 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH31 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH32 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH34 : (PrefixMaximum input n_pre max_value )) (PreH35 : (DecimalExponent exponent )) (PreH36 : (RadixPassState input current exponent )) (PreH37 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH38 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  (0 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) - 1 )) (counters))) (0)))
.

Definition sort_entail_wit_17 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output_2: (@list (@option Z))) (histogram_2: (@list Z)) (current_2: (@list Z)) (counters_2: (@list Z)) (PreH1 : (0 <= (Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (counters_2) (0)) - 1 )) (counters_2))) (0)))) (PreH2 : ((Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (counters_2) (0)) - 1 )) (counters_2))) (0)) < 1000)) (PreH3 : (exponent <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (exponent >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (0 <= (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ))) (PreH8 : ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ) < 10)) (PreH9 : (1 <= (Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (counters_2) (0)))) (PreH10 : ((Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (counters_2) (0)) <= n_pre)) (PreH11 : (max_value <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (max_value >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (i >= 0)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : ((Zlength (input)) = n_pre)) (PreH19 : ((Zlength (current_2)) = n_pre)) (PreH20 : ((Zlength (histogram_2)) = 10)) (PreH21 : ((Zlength (counters_2)) = 10)) (PreH22 : ((Zlength (mixed_output_2)) = 1000)) (PreH23 : (0 <= max_value)) (PreH24 : (max_value <= 999999999)) (PreH25 : (1 <= exponent)) (PreH26 : (exponent <= 100000000)) (PreH27 : (0 < (max_value ÷ exponent ))) (PreH28 : ((-1) <= i)) (PreH29 : (i < n_pre)) (PreH30 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH31 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current_2) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current_2) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH32 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram_2) (0))) /\ ((Znth (digit) (histogram_2) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters_2) (0)))) /\ ((Znth (digit) (counters_2) (0)) <= n_pre)))) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (counters_2) (0))) /\ ((Znth ((((Znth (k_3) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (counters_2) (0)) <= n_pre)))) (PreH34 : (PrefixMaximum input n_pre max_value )) (PreH35 : (DecimalExponent exponent )) (PreH36 : (RadixPassState input current_2 exponent )) (PreH37 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2 )) (PreH38 : (BucketPlacementProgress current_2 exponent (i + 1 ) histogram_2 counters_2 mixed_output_2 )) ,
  (IntArray.mixed_full ( &( "output" ) ) 1000 (replace_Znth ((Znth (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ) (replace_Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ) counters_2 0) - 1 )) (counters_2)) 0)) ((Some ((Znth i current_2 0)))) (mixed_output_2)) )
  **  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.full ( &( "count" ) ) 10 (replace_Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ) counters_2 0) - 1 )) (counters_2)) )
|--
  EX (mixed_output: (@list (@option Z)))  (counters: (@list Z))  (histogram: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength (counters)) = 10) ” 
  &&  “ ((Zlength (mixed_output)) = 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= (i - 1 ))) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (BucketPlacementProgress current exponent ((i - 1 ) + 1 ) histogram counters mixed_output ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output_2: (@list (@option Z))) (histogram_2: (@list Z)) (current_2: (@list Z)) (counters_2: (@list Z)) (PreH1 : (0 <= (Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (counters_2) (0)) - 1 )) (counters_2))) (0)))) (PreH2 : ((Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (counters_2) (0)) - 1 )) (counters_2))) (0)) < 1000)) (PreH3 : (exponent <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (exponent >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (0 <= (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ))) (PreH8 : ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ) < 10)) (PreH9 : (1 <= (Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (counters_2) (0)))) (PreH10 : ((Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (counters_2) (0)) <= n_pre)) (PreH11 : (max_value <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (max_value >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (i >= 0)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : ((Zlength (input)) = n_pre)) (PreH19 : ((Zlength (current_2)) = n_pre)) (PreH20 : ((Zlength (histogram_2)) = 10)) (PreH21 : ((Zlength (counters_2)) = 10)) (PreH22 : ((Zlength (mixed_output_2)) = 1000)) (PreH23 : (0 <= max_value)) (PreH24 : (max_value <= 999999999)) (PreH25 : (1 <= exponent)) (PreH26 : (exponent <= 100000000)) (PreH27 : (0 < (max_value ÷ exponent ))) (PreH28 : ((-1) <= i)) (PreH29 : (i < n_pre)) (PreH30 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH31 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current_2) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current_2) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH32 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram_2) (0))) /\ ((Znth (digit) (histogram_2) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters_2) (0)))) /\ ((Znth (digit) (counters_2) (0)) <= n_pre)))) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (counters_2) (0))) /\ ((Znth ((((Znth (k_3) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (counters_2) (0)) <= n_pre)))) (PreH34 : (PrefixMaximum input n_pre max_value )) (PreH35 : (DecimalExponent exponent )) (PreH36 : (RadixPassState input current_2 exponent )) (PreH37 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2 )) (PreH38 : (BucketPlacementProgress current_2 exponent (i + 1 ) histogram_2 counters_2 mixed_output_2 )) ,
  TT && emp 
|--
  EX (histogram: (@list Z)) ,
  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength ((replace_Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ) counters_2 0) - 1 )) (counters_2)))) = 10) ” 
  &&  “ ((Zlength ((replace_Znth ((Znth (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ) (replace_Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ) counters_2 0) - 1 )) (counters_2)) 0)) ((Some ((Znth i current_2 0)))) (mixed_output_2)))) = 1000) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < (Zlength (input))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= (Zlength (input)))) /\ (0 <= (Znth (digit) ((replace_Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ) counters_2 0) - 1 )) (counters_2))) (0)))) /\ ((Znth (digit) ((replace_Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ) counters_2 0) - 1 )) (counters_2))) (0)) <= (Zlength (input))))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= (i - 1 ))) -> ((1 <= (Znth ((((Znth (k_3) (current_2) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ) counters_2 0) - 1 )) (counters_2))) (0))) /\ ((Znth ((((Znth (k_3) (current_2) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ) counters_2 0) - 1 )) (counters_2))) (0)) <= (Zlength (input))))) ” 
  &&  “ (DigitHistogramPrefix current_2 exponent (Zlength (input)) histogram ) ” 
  &&  “ (BucketPlacementProgress current_2 exponent ((i - 1 ) + 1 ) histogram (replace_Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ) counters_2 0) - 1 )) (counters_2)) (replace_Znth ((Znth (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ) (replace_Znth ((((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current_2) (0)) ÷ exponent ) % ( 10 ) ) counters_2 0) - 1 )) (counters_2)) 0)) ((Some ((Znth i current_2 0)))) (mixed_output_2)) ) ”
  &&  emp
).

Definition sort_entail_wit_18 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (counters: (@list Z)) (histogram_2: (@list Z)) (current_2: (@list Z)) (PreH1 : (i < 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (histogram_2)) = 10)) (PreH7 : ((Zlength (counters)) = 10)) (PreH8 : ((Zlength (mixed_output)) = 1000)) (PreH9 : (0 <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : (0 < (max_value ÷ exponent ))) (PreH14 : ((-1) <= i)) (PreH15 : (i < n_pre)) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((0 <= (Znth (k_4) (current_2) (0))) /\ ((Znth (k_4) (current_2) (0)) <= 999999999)) /\ (0 <= (((Znth (k_4) (current_2) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_4) (current_2) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH18 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram_2) (0))) /\ ((Znth (digit) (histogram_2) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 <= i)) -> ((1 <= (Znth ((((Znth (k_5) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_5) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH20 : (PrefixMaximum input n_pre max_value )) (PreH21 : (DecimalExponent exponent )) (PreH22 : (RadixPassState input current_2 exponent )) (PreH23 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2 )) (PreH24 : (BucketPlacementProgress current_2 exponent (i + 1 ) histogram_2 counters mixed_output )) ,
  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  EX (pass_output: (@list Z))  (bucket_starts: (@list Z))  (histogram: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength (bucket_starts)) = 10) ” 
  &&  “ ((Zlength (pass_output)) = n_pre) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (pass_output) (0)))) /\ ((Znth (k_2) (pass_output) (0)) <= 999999999))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (StableDigitPass current pass_output exponent ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (counters: (@list Z)) (histogram_2: (@list Z)) (current_2: (@list Z)) (PreH1 : (i < 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (histogram_2)) = 10)) (PreH7 : ((Zlength (counters)) = 10)) (PreH8 : ((Zlength (mixed_output)) = 1000)) (PreH9 : (0 <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : (0 < (max_value ÷ exponent ))) (PreH14 : ((-1) <= i)) (PreH15 : (i < n_pre)) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((0 <= (Znth (k_4) (current_2) (0))) /\ ((Znth (k_4) (current_2) (0)) <= 999999999)) /\ (0 <= (((Znth (k_4) (current_2) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_4) (current_2) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH18 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram_2) (0))) /\ ((Znth (digit) (histogram_2) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 <= i)) -> ((1 <= (Znth ((((Znth (k_5) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_5) (current_2) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH20 : (PrefixMaximum input n_pre max_value )) (PreH21 : (DecimalExponent exponent )) (PreH22 : (RadixPassState input current_2 exponent )) (PreH23 : (DigitHistogramPrefix current_2 exponent n_pre histogram_2 )) (PreH24 : (BucketPlacementProgress current_2 exponent (i + 1 ) histogram_2 counters mixed_output )) ,
  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  EX (pass_output: (@list Z))  (histogram: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current_2)) = n_pre) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength (counters)) = 10) ” 
  &&  “ ((Zlength (pass_output)) = n_pre) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (pass_output) (0)))) /\ ((Znth (k_2) (pass_output) (0)) <= 999999999))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current_2 exponent ) ” 
  &&  “ (DigitHistogramPrefix current_2 exponent n_pre histogram ) ” 
  &&  “ (StableDigitPass current_2 pass_output exponent ) ”
  &&  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
).

Definition sort_entail_wit_19 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (histogram: (@list Z)) (bucket_starts_2: (@list Z)) (pass_output_2: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (histogram)) = 10)) (PreH6 : ((Zlength (bucket_starts_2)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : (0 < (max_value ÷ exponent ))) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH14 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((0 <= (Znth (k_4) (current_2) (0))) /\ ((Znth (k_4) (current_2) (0)) <= 999999999)) /\ (0 <= (Znth (k_4) (pass_output_2) (0)))) /\ ((Znth (k_4) (pass_output_2) (0)) <= 999999999)))) (PreH15 : (PrefixMaximum input n_pre max_value )) (PreH16 : (DecimalExponent exponent )) (PreH17 : (RadixPassState input current_2 exponent )) (PreH18 : (DigitHistogramPrefix current_2 exponent n_pre histogram )) (PreH19 : (StableDigitPass current_2 pass_output_2 exponent )) ,
  (IntArray.full a_pre n_pre current_2 )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts_2 )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output_2 )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  EX (working: (@list Z))  (pass_output: (@list Z))  (bucket_starts: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (bucket_starts)) = 10) ” 
  &&  “ ((Zlength (pass_output)) = n_pre) ” 
  &&  “ ((Zlength (working)) = n_pre) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (pass_output) (0)))) /\ ((Znth (k_2) (pass_output) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (working) (0)))) /\ ((Znth (k_2) (working) (0)) <= 999999999))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (StableDigitPass current pass_output exponent ) ” 
  &&  “ (RadixCopyPrefix current pass_output working 0 ) ”
  &&  (IntArray.full a_pre n_pre working )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (current_2: (@list Z)) (histogram: (@list Z)) (bucket_starts_2: (@list Z)) (pass_output_2: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (current_2)) = n_pre)) (PreH5 : ((Zlength (histogram)) = 10)) (PreH6 : ((Zlength (bucket_starts_2)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : (0 < (max_value ÷ exponent ))) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH14 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((0 <= (Znth (k_4) (current_2) (0))) /\ ((Znth (k_4) (current_2) (0)) <= 999999999)) /\ (0 <= (Znth (k_4) (pass_output_2) (0)))) /\ ((Znth (k_4) (pass_output_2) (0)) <= 999999999)))) (PreH15 : (PrefixMaximum input n_pre max_value )) (PreH16 : (DecimalExponent exponent )) (PreH17 : (RadixPassState input current_2 exponent )) (PreH18 : (DigitHistogramPrefix current_2 exponent n_pre histogram )) (PreH19 : (StableDigitPass current_2 pass_output_2 exponent )) ,
  TT && emp 
|--
  EX (current: (@list Z)) ,
  “ ((Zlength (current)) = (Zlength (input))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength (input))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (Zlength (input)))) -> ((((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (pass_output_2) (0)))) /\ ((Znth (k_2) (pass_output_2) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (current_2) (0)))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999))) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (StableDigitPass current pass_output_2 exponent ) ” 
  &&  “ (RadixCopyPrefix current pass_output_2 current_2 0 ) ”
  &&  emp
).

Definition sort_entail_wit_20 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (working_2: (@list Z)) (pass_output_2: (@list Z)) (bucket_starts_2: (@list Z)) (current_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (bucket_starts_2)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : ((Zlength (working_2)) = n_pre)) (PreH9 : (0 <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : (0 < (max_value ÷ exponent ))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (pass_output_2) (0)))) /\ ((Znth (k_2) (pass_output_2) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (working_2) (0)))) /\ ((Znth (k_2) (working_2) (0)) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current_2 exponent )) (PreH21 : (StableDigitPass current_2 pass_output_2 exponent )) (PreH22 : (RadixCopyPrefix current_2 pass_output_2 working_2 i )) ,
  (IntArray.full a_pre n_pre (replace_Znth (i) ((Znth (i - 0 ) pass_output_2 0)) (working_2)) )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output_2 )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts_2 )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  EX (working: (@list Z))  (pass_output: (@list Z))  (bucket_starts: (@list Z))  (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (bucket_starts)) = 10) ” 
  &&  “ ((Zlength (pass_output)) = n_pre) ” 
  &&  “ ((Zlength (working)) = n_pre) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (pass_output) (0)))) /\ ((Znth (k_2) (pass_output) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (working) (0)))) /\ ((Znth (k_2) (working) (0)) <= 999999999))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (StableDigitPass current pass_output exponent ) ” 
  &&  “ (RadixCopyPrefix current pass_output working (i + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre working )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (working_2: (@list Z)) (pass_output_2: (@list Z)) (bucket_starts_2: (@list Z)) (current_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current_2)) = n_pre)) (PreH6 : ((Zlength (bucket_starts_2)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : ((Zlength (working_2)) = n_pre)) (PreH9 : (0 <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : (0 < (max_value ÷ exponent ))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((0 <= (Znth (k_2) (current_2) (0))) /\ ((Znth (k_2) (current_2) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (pass_output_2) (0)))) /\ ((Znth (k_2) (pass_output_2) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (working_2) (0)))) /\ ((Znth (k_2) (working_2) (0)) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current_2 exponent )) (PreH21 : (StableDigitPass current_2 pass_output_2 exponent )) (PreH22 : (RadixCopyPrefix current_2 pass_output_2 working_2 i )) ,
  TT && emp 
|--
  EX (current: (@list Z)) ,
  “ ((Zlength (current)) = (Zlength (input))) ” 
  &&  “ ((Zlength ((replace_Znth (i) ((Znth (i - 0 ) pass_output_2 0)) (working_2)))) = (Zlength (input))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (input))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (Zlength (input)))) -> ((((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (pass_output_2) (0)))) /\ ((Znth (k_2) (pass_output_2) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) ((replace_Znth (i) ((Znth (i - 0 ) pass_output_2 0)) (working_2))) (0)))) /\ ((Znth (k_2) ((replace_Znth (i) ((Znth (i - 0 ) pass_output_2 0)) (working_2))) (0)) <= 999999999))) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (StableDigitPass current pass_output_2 exponent ) ” 
  &&  “ (RadixCopyPrefix current pass_output_2 (replace_Znth (i) ((Znth (i - 0 ) pass_output_2 0)) (working_2)) (i + 1 ) ) ”
  &&  emp
).

Definition sort_entail_wit_21 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (working: (@list Z)) (pass_output_2: (@list Z)) (bucket_starts: (@list Z)) (current: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : ((Zlength (working)) = n_pre)) (PreH9 : (0 <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : (0 < (max_value ÷ exponent ))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((((0 <= (Znth (k_4) (current) (0))) /\ ((Znth (k_4) (current) (0)) <= 999999999)) /\ (0 <= (Znth (k_4) (pass_output_2) (0)))) /\ ((Znth (k_4) (pass_output_2) (0)) <= 999999999)) /\ (0 <= (Znth (k_4) (working) (0)))) /\ ((Znth (k_4) (working) (0)) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (StableDigitPass current pass_output_2 exponent )) (PreH22 : (RadixCopyPrefix current pass_output_2 working i )) ,
  (IntArray.full a_pre n_pre working )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output_2 )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  EX (pass_output: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (pass_output)) = n_pre) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (1 <= (exponent * 10 )) ” 
  &&  “ ((exponent * 10 ) <= 1000000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (pass_output) (0))) /\ ((Znth (k_2) (pass_output) (0)) <= 999999999))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent (exponent * 10 ) ) ” 
  &&  “ (RadixPassState input pass_output (exponent * 10 ) ) ”
  &&  (IntArray.full a_pre n_pre pass_output )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (working: (@list Z)) (pass_output_2: (@list Z)) (bucket_starts: (@list Z)) (current: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : ((Zlength (working)) = n_pre)) (PreH9 : (0 <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : (0 < (max_value ÷ exponent ))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((((0 <= (Znth (k_4) (current) (0))) /\ ((Znth (k_4) (current) (0)) <= 999999999)) /\ (0 <= (Znth (k_4) (pass_output_2) (0)))) /\ ((Znth (k_4) (pass_output_2) (0)) <= 999999999)) /\ (0 <= (Znth (k_4) (working) (0)))) /\ ((Znth (k_4) (working) (0)) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (StableDigitPass current pass_output_2 exponent )) (PreH22 : (RadixCopyPrefix current pass_output_2 working i )) ,
  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output_2 )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  “ (RadixPassState input working (exponent * 10 ) ) ” 
  &&  “ (DecimalExponent (exponent * 10 ) ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (working) (0))) /\ ((Znth (k_2) (working) (0)) <= 999999999))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ”
  &&  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
).

Definition sort_entail_wit_21_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (working: (@list Z)) (pass_output_2: (@list Z)) (bucket_starts: (@list Z)) (current: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : ((Zlength (working)) = n_pre)) (PreH9 : (0 <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : (0 < (max_value ÷ exponent ))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((((0 <= (Znth (k_4) (current) (0))) /\ ((Znth (k_4) (current) (0)) <= 999999999)) /\ (0 <= (Znth (k_4) (pass_output_2) (0)))) /\ ((Znth (k_4) (pass_output_2) (0)) <= 999999999)) /\ (0 <= (Znth (k_4) (working) (0)))) /\ ((Znth (k_4) (working) (0)) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (StableDigitPass current pass_output_2 exponent )) (PreH22 : (RadixCopyPrefix current pass_output_2 working i )) ,
  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output_2 )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  “ (RadixPassState input working (exponent * 10 ) ) ”
.

Definition sort_entail_wit_21_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (working: (@list Z)) (pass_output_2: (@list Z)) (bucket_starts: (@list Z)) (current: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : ((Zlength (working)) = n_pre)) (PreH9 : (0 <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : (0 < (max_value ÷ exponent ))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((((0 <= (Znth (k_4) (current) (0))) /\ ((Znth (k_4) (current) (0)) <= 999999999)) /\ (0 <= (Znth (k_4) (pass_output_2) (0)))) /\ ((Znth (k_4) (pass_output_2) (0)) <= 999999999)) /\ (0 <= (Znth (k_4) (working) (0)))) /\ ((Znth (k_4) (working) (0)) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (StableDigitPass current pass_output_2 exponent )) (PreH22 : (RadixCopyPrefix current pass_output_2 working i )) ,
  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output_2 )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  “ (DecimalExponent (exponent * 10 ) ) ”
.

Definition sort_entail_wit_21_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (working: (@list Z)) (pass_output_2: (@list Z)) (bucket_starts: (@list Z)) (current: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : ((Zlength (working)) = n_pre)) (PreH9 : (0 <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : (0 < (max_value ÷ exponent ))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((((0 <= (Znth (k_4) (current) (0))) /\ ((Znth (k_4) (current) (0)) <= 999999999)) /\ (0 <= (Znth (k_4) (pass_output_2) (0)))) /\ ((Znth (k_4) (pass_output_2) (0)) <= 999999999)) /\ (0 <= (Znth (k_4) (working) (0)))) /\ ((Znth (k_4) (working) (0)) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (StableDigitPass current pass_output_2 exponent )) (PreH22 : (RadixCopyPrefix current pass_output_2 working i )) ,
  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output_2 )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (working) (0))) /\ ((Znth (k_2) (working) (0)) <= 999999999))) ”
.

Definition sort_entail_wit_21_split_goal_4 := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (working: (@list Z)) (pass_output_2: (@list Z)) (bucket_starts: (@list Z)) (current: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : ((Zlength (working)) = n_pre)) (PreH9 : (0 <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : (0 < (max_value ÷ exponent ))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((((0 <= (Znth (k_4) (current) (0))) /\ ((Znth (k_4) (current) (0)) <= 999999999)) /\ (0 <= (Znth (k_4) (pass_output_2) (0)))) /\ ((Znth (k_4) (pass_output_2) (0)) <= 999999999)) /\ (0 <= (Znth (k_4) (working) (0)))) /\ ((Znth (k_4) (working) (0)) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (StableDigitPass current pass_output_2 exponent )) (PreH22 : (RadixCopyPrefix current pass_output_2 working i )) ,
  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output_2 )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ”
.

Definition sort_entail_wit_21_split_goal_spatial := 
forall (n_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (working: (@list Z)) (pass_output_2: (@list Z)) (bucket_starts: (@list Z)) (current: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output_2)) = n_pre)) (PreH8 : ((Zlength (working)) = n_pre)) (PreH9 : (0 <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : (0 < (max_value ÷ exponent ))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH17 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((((0 <= (Znth (k_4) (current) (0))) /\ ((Znth (k_4) (current) (0)) <= 999999999)) /\ (0 <= (Znth (k_4) (pass_output_2) (0)))) /\ ((Znth (k_4) (pass_output_2) (0)) <= 999999999)) /\ (0 <= (Znth (k_4) (working) (0)))) /\ ((Znth (k_4) (working) (0)) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (StableDigitPass current pass_output_2 exponent )) (PreH22 : (RadixCopyPrefix current pass_output_2 working i )) ,
  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output_2 )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
.

Definition sort_entail_wit_22 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (pass_output: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (pass_output)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (1 <= (exponent * 10 ))) (PreH10 : ((exponent * 10 ) <= 1000000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (pass_output) (0))) /\ ((Znth (k_4) (pass_output) (0)) <= 999999999)))) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent (exponent * 10 ) )) (PreH16 : (RadixPassState input pass_output (exponent * 10 ) )) ,
  (IntArray.full a_pre n_pre pass_output )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
|--
  EX (current: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= (exponent * 10 )) ” 
  &&  “ ((exponent * 10 ) <= 1000000000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent (exponent * 10 ) ) ” 
  &&  “ (RadixPassState input current (exponent * 10 ) ) ”
  &&  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (pass_output: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (pass_output)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (1 <= (exponent * 10 ))) (PreH10 : ((exponent * 10 ) <= 1000000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (pass_output) (0))) /\ ((Znth (k_4) (pass_output) (0)) <= 999999999)))) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent (exponent * 10 ) )) (PreH16 : (RadixPassState input pass_output (exponent * 10 ) )) ,
  TT && emp 
|--
  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (pass_output) (0))) /\ ((Znth (k_2) (pass_output) (0)) <= 999999999))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ”
  &&  emp
).

Definition sort_entail_wit_22_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (pass_output: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (pass_output)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (1 <= (exponent * 10 ))) (PreH10 : ((exponent * 10 ) <= 1000000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (pass_output) (0))) /\ ((Znth (k_4) (pass_output) (0)) <= 999999999)))) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent (exponent * 10 ) )) (PreH16 : (RadixPassState input pass_output (exponent * 10 ) )) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (pass_output) (0))) /\ ((Znth (k_2) (pass_output) (0)) <= 999999999)))
.

Definition sort_entail_wit_22_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (pass_output: (@list Z)) (max_value: Z) (exponent: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (pass_output)) = n_pre)) (PreH5 : (0 <= max_value)) (PreH6 : (max_value <= 999999999)) (PreH7 : (1 <= exponent)) (PreH8 : (exponent <= 100000000)) (PreH9 : (1 <= (exponent * 10 ))) (PreH10 : ((exponent * 10 ) <= 1000000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (input) (0))) /\ ((Znth (k_3) (input) (0)) <= 999999999)))) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth (k_4) (pass_output) (0))) /\ ((Znth (k_4) (pass_output) (0)) <= 999999999)))) (PreH14 : (PrefixMaximum input n_pre max_value )) (PreH15 : (DecimalExponent (exponent * 10 ) )) (PreH16 : (RadixPassState input pass_output (exponent * 10 ) )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))
.

Definition sort_entail_wit_23 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (current: (@list Z)) (PreH1 : ((max_value ÷ exponent ) <= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (input) (0))) /\ ((Znth (k_2) (input) (0)) <= 999999999)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (current) (0))) /\ ((Znth (k_3) (current) (0)) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value )) (PreH13 : (DecimalExponent exponent )) (PreH14 : (RadixPassState input current exponent )) ,
  ((( &( "max_value" ) )) # Int  |-> max_value)
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
|--
  EX (final: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (final)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ (Permutation input final ) ” 
  &&  “ (increasing final ) ”
  &&  (IntArray.full a_pre n_pre final )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
  **  (IntArray.undef_full ( &( "count" ) ) 10 )
  **  ((( &( "max_value" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (current: (@list Z)) (PreH1 : ((max_value ÷ exponent ) <= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (input) (0))) /\ ((Znth (k_2) (input) (0)) <= 999999999)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (current) (0))) /\ ((Znth (k_3) (current) (0)) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value )) (PreH13 : (DecimalExponent exponent )) (PreH14 : (RadixPassState input current exponent )) ,
  TT && emp 
|--
  “ (increasing current ) ” 
  &&  “ (Permutation input current ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ”
  &&  emp
).

Definition sort_entail_wit_23_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (current: (@list Z)) (PreH1 : ((max_value ÷ exponent ) <= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (input) (0))) /\ ((Znth (k_2) (input) (0)) <= 999999999)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (current) (0))) /\ ((Znth (k_3) (current) (0)) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value )) (PreH13 : (DecimalExponent exponent )) (PreH14 : (RadixPassState input current exponent )) ,
  (increasing current )
.

Definition sort_entail_wit_23_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (current: (@list Z)) (PreH1 : ((max_value ÷ exponent ) <= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (input) (0))) /\ ((Znth (k_2) (input) (0)) <= 999999999)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (current) (0))) /\ ((Znth (k_3) (current) (0)) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value )) (PreH13 : (DecimalExponent exponent )) (PreH14 : (RadixPassState input current exponent )) ,
  (Permutation input current )
.

Definition sort_entail_wit_23_split_goal_3 := 
forall (n_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (current: (@list Z)) (PreH1 : ((max_value ÷ exponent ) <= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : (0 <= max_value)) (PreH7 : (max_value <= 999999999)) (PreH8 : (1 <= exponent)) (PreH9 : (exponent <= 1000000000)) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (input) (0))) /\ ((Znth (k_2) (input) (0)) <= 999999999)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth (k_3) (current) (0))) /\ ((Znth (k_3) (current) (0)) <= 999999999)))) (PreH12 : (PrefixMaximum input n_pre max_value )) (PreH13 : (DecimalExponent exponent )) (PreH14 : (RadixPassState input current exponent )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))
.

Definition sort_return_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre <= 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth (i) (input) (0))) /\ ((Znth (i) (input) (0)) <= 999999999)))) ,
  (IntArray.full a_pre n_pre input )
|--
  EX (output: (@list Z)) ,
  “ ((Zlength (output)) = n_pre) ” 
  &&  “ (Permutation input output ) ” 
  &&  “ (increasing output ) ”
  &&  (IntArray.full a_pre n_pre output )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre <= 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth (i) (input) (0))) /\ ((Znth (i) (input) (0)) <= 999999999)))) ,
  TT && emp 
|--
  “ (increasing input ) ” 
  &&  “ (Permutation input input ) ”
  &&  emp
).

Definition sort_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre <= 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth (i) (input) (0))) /\ ((Znth (i) (input) (0)) <= 999999999)))) ,
  (increasing input )
.

Definition sort_return_wit_1_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (PreH1 : (n_pre <= 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth (i) (input) (0))) /\ ((Znth (i) (input) (0)) <= 999999999)))) ,
  (Permutation input input )
.

Definition sort_return_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (final: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : ((Zlength (final)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH6 : (Permutation input final )) (PreH7 : (increasing final )) ,
  (IntArray.full a_pre n_pre final )
|--
  EX (output: (@list Z)) ,
  “ ((Zlength (output)) = n_pre) ” 
  &&  “ (Permutation input output ) ” 
  &&  “ (increasing output ) ”
  &&  (IntArray.full a_pre n_pre output )
.

Definition sort_partial_solve_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre > 1)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth (i) (input) (0))) /\ ((Znth (i) (input) (0)) <= 999999999)))) ,
  (IntArray.full a_pre n_pre input )
|--
  “ (n_pre > 1) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth (i) (input) (0))) /\ ((Znth (i) (input) (0)) <= 999999999))) ”
  &&  (((a_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 input 0))
  **  (IntArray.missing_i a_pre 0 0 n_pre input )
.

Definition sort_partial_solve_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH10 : (PrefixMaximum input i max_value )) ,
  (IntArray.full a_pre n_pre input )
|--
  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ (PrefixMaximum input i max_value ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i a_pre i 0 n_pre input )
.

Definition sort_partial_solve_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (max_value: Z) (i: Z) (PreH1 : ((Znth i input 0) > max_value)) (PreH2 : (i < n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH11 : (PrefixMaximum input i max_value )) ,
  (IntArray.full a_pre n_pre input )
|--
  “ ((Znth i input 0) > max_value) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ (PrefixMaximum input i max_value ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i a_pre i 0 n_pre input )
.

Definition sort_partial_solve_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (exponent: Z) (max_value: Z) (digit: Z) (zero_prefix: (@list Z)) (current: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (zero_prefix)) = digit)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : (0 <= digit)) (PreH13 : (digit <= 10)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < digit)) -> ((Znth (k_3) (zero_prefix) (0)) = 0))) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current exponent )) ,
  (IntArray.full a_pre n_pre current )
  **  (IntArray.seg ( &( "count" ) ) 0 digit zero_prefix )
  **  (IntArray.undef_seg ( &( "count" ) ) digit 10 )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (digit < 10) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (zero_prefix)) = digit) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= digit) ” 
  &&  “ (digit <= 10) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < digit)) -> ((Znth (k_3) (zero_prefix) (0)) = 0)) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ”
  &&  (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "count" ) ) (digit + 1 ) 10 )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.seg ( &( "count" ) ) 0 digit zero_prefix )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
.

Definition sort_partial_solve_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (counts)) = 10)) (PreH7 : (0 <= max_value)) (PreH8 : (max_value <= 999999999)) (PreH9 : (1 <= exponent)) (PreH10 : (exponent <= 100000000)) (PreH11 : (0 < (max_value ÷ exponent ))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH16 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= i)))) (PreH17 : (PrefixMaximum input n_pre max_value )) (PreH18 : (DecimalExponent exponent )) (PreH19 : (RadixPassState input current exponent )) (PreH20 : (DigitHistogramPrefix current exponent i counts )) ,
  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= i))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent i counts ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i current 0))
  **  (IntArray.missing_i a_pre i 0 n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
.

Definition sort_partial_solve_wit_6 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current: (@list Z)) (PreH1 : (0 <= (((Znth i current 0) ÷ exponent ) % ( 10 ) ))) (PreH2 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (counts)) = 10)) (PreH17 : (0 <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : (0 < (max_value ÷ exponent ))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH26 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value )) (PreH28 : (DecimalExponent exponent )) (PreH29 : (RadixPassState input current exponent )) (PreH30 : (DigitHistogramPrefix current exponent i counts )) ,
  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (0 <= (((Znth i current 0) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) < 10) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (exponent <= INT_MAX) ” 
  &&  “ (max_value <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (exponent >= INT_MIN) ” 
  &&  “ (max_value >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= i))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent i counts ) ”
  &&  (((( &( "count" ) ) + ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) * sizeof(INT)))) # Int  |-> (Znth (((Znth i current 0) ÷ exponent ) % ( 10 ) ) counts 0))
  **  (IntArray.missing_i ( &( "count" ) ) (((Znth i current 0) ÷ exponent ) % ( 10 ) ) 0 10 counts )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
.

Definition sort_partial_solve_wit_7 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (counts: (@list Z)) (current: (@list Z)) (PreH1 : (0 <= (((Znth i current 0) ÷ exponent ) % ( 10 ) ))) (PreH2 : ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) < 10)) (PreH3 : (i <= INT_MAX)) (PreH4 : (exponent <= INT_MAX)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (exponent >= INT_MIN)) (PreH9 : (max_value >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : ((Zlength (input)) = n_pre)) (PreH15 : ((Zlength (current)) = n_pre)) (PreH16 : ((Zlength (counts)) = 10)) (PreH17 : (0 <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : (0 < (max_value ÷ exponent ))) (PreH22 : (0 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH26 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= i)))) (PreH27 : (PrefixMaximum input n_pre max_value )) (PreH28 : (DecimalExponent exponent )) (PreH29 : (RadixPassState input current exponent )) (PreH30 : (DigitHistogramPrefix current exponent i counts )) ,
  (IntArray.full ( &( "count" ) ) 10 counts )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (0 <= (((Znth i current 0) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) < 10) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (exponent <= INT_MAX) ” 
  &&  “ (max_value <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (exponent >= INT_MIN) ” 
  &&  “ (max_value >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((0 <= (Znth (digit) (counts) (0))) /\ ((Znth (digit) (counts) (0)) <= i))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent i counts ) ”
  &&  (((( &( "count" ) ) + ((((Znth i current 0) ÷ exponent ) % ( 10 ) ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "count" ) ) (((Znth i current 0) ÷ exponent ) % ( 10 ) ) 0 10 counts )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
.

Definition sort_partial_solve_wit_8 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (totals: (@list Z)) (histogram: (@list Z)) (current: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : (0 < (max_value ÷ exponent ))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 10)) -> ((0 <= (Znth (k_3) (histogram) (0))) /\ ((Znth (k_3) (histogram) (0)) <= n_pre)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 10)) -> ((0 <= (Znth (k_4) (totals) (0))) /\ ((Znth (k_4) (totals) (0)) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value )) (PreH20 : (DecimalExponent exponent )) (PreH21 : (RadixPassState input current exponent )) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH23 : (DigitPrefixTotals histogram totals digit )) ,
  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 totals )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (digit < 10) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength (totals)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (1 <= digit) ” 
  &&  “ (digit <= 10) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 10)) -> ((0 <= (Znth (k_3) (histogram) (0))) /\ ((Znth (k_3) (histogram) (0)) <= n_pre))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 10)) -> ((0 <= (Znth (k_4) (totals) (0))) /\ ((Znth (k_4) (totals) (0)) <= n_pre))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (DigitPrefixTotals histogram totals digit ) ”
  &&  (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int  |-> (Znth digit totals 0))
  **  (IntArray.missing_i ( &( "count" ) ) digit 0 10 totals )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
.

Definition sort_partial_solve_wit_9 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (totals: (@list Z)) (histogram: (@list Z)) (current: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : (0 < (max_value ÷ exponent ))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 10)) -> ((0 <= (Znth (k_3) (histogram) (0))) /\ ((Znth (k_3) (histogram) (0)) <= n_pre)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 10)) -> ((0 <= (Znth (k_4) (totals) (0))) /\ ((Znth (k_4) (totals) (0)) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value )) (PreH20 : (DecimalExponent exponent )) (PreH21 : (RadixPassState input current exponent )) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH23 : (DigitPrefixTotals histogram totals digit )) ,
  (IntArray.full ( &( "count" ) ) 10 totals )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (digit < 10) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength (totals)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (1 <= digit) ” 
  &&  “ (digit <= 10) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 10)) -> ((0 <= (Znth (k_3) (histogram) (0))) /\ ((Znth (k_3) (histogram) (0)) <= n_pre))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 10)) -> ((0 <= (Znth (k_4) (totals) (0))) /\ ((Znth (k_4) (totals) (0)) <= n_pre))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (DigitPrefixTotals histogram totals digit ) ”
  &&  (((( &( "count" ) ) + ((digit - 1 ) * sizeof(INT)))) # Int  |-> (Znth (digit - 1 ) totals 0))
  **  (IntArray.missing_i ( &( "count" ) ) (digit - 1 ) 0 10 totals )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
.

Definition sort_partial_solve_wit_10 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (digit: Z) (exponent: Z) (max_value: Z) (totals: (@list Z)) (histogram: (@list Z)) (current: (@list Z)) (PreH1 : (digit < 10)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (totals)) = 10)) (PreH8 : (0 <= max_value)) (PreH9 : (max_value <= 999999999)) (PreH10 : (1 <= exponent)) (PreH11 : (exponent <= 100000000)) (PreH12 : (0 < (max_value ÷ exponent ))) (PreH13 : (1 <= digit)) (PreH14 : (digit <= 10)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 10)) -> ((0 <= (Znth (k_3) (histogram) (0))) /\ ((Znth (k_3) (histogram) (0)) <= n_pre)))) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 10)) -> ((0 <= (Znth (k_4) (totals) (0))) /\ ((Znth (k_4) (totals) (0)) <= n_pre)))) (PreH19 : (PrefixMaximum input n_pre max_value )) (PreH20 : (DecimalExponent exponent )) (PreH21 : (RadixPassState input current exponent )) (PreH22 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH23 : (DigitPrefixTotals histogram totals digit )) ,
  (IntArray.full ( &( "count" ) ) 10 totals )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
|--
  “ (digit < 10) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength (totals)) = 10) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (1 <= digit) ” 
  &&  “ (digit <= 10) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 10)) -> ((0 <= (Znth (k_3) (histogram) (0))) /\ ((Znth (k_3) (histogram) (0)) <= n_pre))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < 10)) -> ((0 <= (Znth (k_4) (totals) (0))) /\ ((Znth (k_4) (totals) (0)) <= n_pre))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (DigitPrefixTotals histogram totals digit ) ”
  &&  (((( &( "count" ) ) + (digit * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "count" ) ) digit 0 10 totals )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.undef_full ( &( "output" ) ) 1000 )
.

Definition sort_partial_solve_wit_11 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (histogram)) = 10)) (PreH7 : ((Zlength (counters)) = 10)) (PreH8 : ((Zlength (mixed_output)) = 1000)) (PreH9 : (0 <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : (0 < (max_value ÷ exponent ))) (PreH14 : ((-1) <= i)) (PreH15 : (i < n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH18 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH19 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH20 : (PrefixMaximum input n_pre max_value )) (PreH21 : (DecimalExponent exponent )) (PreH22 : (RadixPassState input current exponent )) (PreH23 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH24 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ (i >= 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength (counters)) = 10) ” 
  &&  “ ((Zlength (mixed_output)) = 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i current 0))
  **  (IntArray.missing_i a_pre i 0 n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
.

Definition sort_partial_solve_wit_12 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (0 <= (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH2 : ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)) (PreH3 : ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) = (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH4 : (1 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)))) (PreH5 : ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)) (PreH6 : (max_value <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (max_value >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (i >= 0)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : ((Zlength (input)) = n_pre)) (PreH14 : ((Zlength (current)) = n_pre)) (PreH15 : ((Zlength (histogram)) = 10)) (PreH16 : ((Zlength (counters)) = 10)) (PreH17 : ((Zlength (mixed_output)) = 1000)) (PreH18 : (0 <= max_value)) (PreH19 : (max_value <= 999999999)) (PreH20 : (1 <= exponent)) (PreH21 : (exponent <= 100000000)) (PreH22 : (0 < (max_value ÷ exponent ))) (PreH23 : ((-1) <= i)) (PreH24 : (i < n_pre)) (PreH25 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH26 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH27 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH28 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH29 : (PrefixMaximum input n_pre max_value )) (PreH30 : (DecimalExponent exponent )) (PreH31 : (RadixPassState input current exponent )) (PreH32 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH33 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ (0 <= (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10) ” 
  &&  “ (1 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) ” 
  &&  “ ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre) ” 
  &&  “ (max_value <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (max_value >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength (counters)) = 10) ” 
  &&  “ ((Zlength (mixed_output)) = 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output ) ”
  &&  (((( &( "count" ) ) + ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) * sizeof(INT)))) # Int  |-> (Znth (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) counters 0))
  **  (IntArray.missing_i ( &( "count" ) ) (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) 0 10 counters )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
.

Definition sort_partial_solve_wit_13 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (0 <= (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH2 : ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)) (PreH3 : (1 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)))) (PreH4 : ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)) (PreH5 : (max_value <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (max_value >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (i >= 0)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 1000)) (PreH12 : ((Zlength (input)) = n_pre)) (PreH13 : ((Zlength (current)) = n_pre)) (PreH14 : ((Zlength (histogram)) = 10)) (PreH15 : ((Zlength (counters)) = 10)) (PreH16 : ((Zlength (mixed_output)) = 1000)) (PreH17 : (0 <= max_value)) (PreH18 : (max_value <= 999999999)) (PreH19 : (1 <= exponent)) (PreH20 : (exponent <= 100000000)) (PreH21 : (0 < (max_value ÷ exponent ))) (PreH22 : ((-1) <= i)) (PreH23 : (i < n_pre)) (PreH24 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH25 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH26 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH27 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH28 : (PrefixMaximum input n_pre max_value )) (PreH29 : (DecimalExponent exponent )) (PreH30 : (RadixPassState input current exponent )) (PreH31 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH32 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  (IntArray.full ( &( "count" ) ) 10 counters )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ (0 <= (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10) ” 
  &&  “ (1 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) ” 
  &&  “ ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre) ” 
  &&  “ (max_value <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (max_value >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength (counters)) = 10) ” 
  &&  “ ((Zlength (mixed_output)) = 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output ) ”
  &&  (((( &( "count" ) ) + ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "count" ) ) (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) 0 10 counters )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
.

Definition sort_partial_solve_wit_14 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (0 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) - 1 )) (counters))) (0)))) (PreH2 : ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) - 1 )) (counters))) (0)) < 1000)) (PreH3 : (exponent <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (exponent >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (0 <= (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH8 : ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)) (PreH9 : (1 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)))) (PreH10 : ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)) (PreH11 : (max_value <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (max_value >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (i >= 0)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : ((Zlength (input)) = n_pre)) (PreH19 : ((Zlength (current)) = n_pre)) (PreH20 : ((Zlength (histogram)) = 10)) (PreH21 : ((Zlength (counters)) = 10)) (PreH22 : ((Zlength (mixed_output)) = 1000)) (PreH23 : (0 <= max_value)) (PreH24 : (max_value <= 999999999)) (PreH25 : (1 <= exponent)) (PreH26 : (exponent <= 100000000)) (PreH27 : (0 < (max_value ÷ exponent ))) (PreH28 : ((-1) <= i)) (PreH29 : (i < n_pre)) (PreH30 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH31 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH32 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH34 : (PrefixMaximum input n_pre max_value )) (PreH35 : (DecimalExponent exponent )) (PreH36 : (RadixPassState input current exponent )) (PreH37 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH38 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  (IntArray.full ( &( "count" ) ) 10 (replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) counters 0) - 1 )) (counters)) )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ (0 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) - 1 )) (counters))) (0))) ” 
  &&  “ ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) - 1 )) (counters))) (0)) < 1000) ” 
  &&  “ (exponent <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (exponent >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (0 <= (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10) ” 
  &&  “ (1 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) ” 
  &&  “ ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre) ” 
  &&  “ (max_value <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (max_value >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength (counters)) = 10) ” 
  &&  “ ((Zlength (mixed_output)) = 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output ) ”
  &&  (((( &( "count" ) ) + ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) * sizeof(INT)))) # Int  |-> (Znth (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) (replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) counters 0) - 1 )) (counters)) 0))
  **  (IntArray.missing_i ( &( "count" ) ) (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) 0 10 (replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) counters 0) - 1 )) (counters)) )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
.

Definition sort_partial_solve_wit_15 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (0 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) - 1 )) (counters))) (0)))) (PreH2 : ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) - 1 )) (counters))) (0)) < 1000)) (PreH3 : (exponent <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (exponent >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (0 <= (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH8 : ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)) (PreH9 : (1 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)))) (PreH10 : ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)) (PreH11 : (max_value <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (max_value >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (i >= 0)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : ((Zlength (input)) = n_pre)) (PreH19 : ((Zlength (current)) = n_pre)) (PreH20 : ((Zlength (histogram)) = 10)) (PreH21 : ((Zlength (counters)) = 10)) (PreH22 : ((Zlength (mixed_output)) = 1000)) (PreH23 : (0 <= max_value)) (PreH24 : (max_value <= 999999999)) (PreH25 : (1 <= exponent)) (PreH26 : (exponent <= 100000000)) (PreH27 : (0 < (max_value ÷ exponent ))) (PreH28 : ((-1) <= i)) (PreH29 : (i < n_pre)) (PreH30 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH31 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH32 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH34 : (PrefixMaximum input n_pre max_value )) (PreH35 : (DecimalExponent exponent )) (PreH36 : (RadixPassState input current exponent )) (PreH37 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH38 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  (IntArray.full ( &( "count" ) ) 10 (replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) counters 0) - 1 )) (counters)) )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ (0 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) - 1 )) (counters))) (0))) ” 
  &&  “ ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) - 1 )) (counters))) (0)) < 1000) ” 
  &&  “ (exponent <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (exponent >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (0 <= (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10) ” 
  &&  “ (1 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) ” 
  &&  “ ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre) ” 
  &&  “ (max_value <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (max_value >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength (counters)) = 10) ” 
  &&  “ ((Zlength (mixed_output)) = 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i current 0))
  **  (IntArray.missing_i a_pre i 0 n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 (replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) counters 0) - 1 )) (counters)) )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
.

Definition sort_partial_solve_wit_16 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (mixed_output: (@list (@option Z))) (histogram: (@list Z)) (current: (@list Z)) (counters: (@list Z)) (PreH1 : (0 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) - 1 )) (counters))) (0)))) (PreH2 : ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) - 1 )) (counters))) (0)) < 1000)) (PreH3 : (exponent <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (exponent >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (0 <= (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ))) (PreH8 : ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)) (PreH9 : (1 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)))) (PreH10 : ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)) (PreH11 : (max_value <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (max_value >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (i >= 0)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : ((Zlength (input)) = n_pre)) (PreH19 : ((Zlength (current)) = n_pre)) (PreH20 : ((Zlength (histogram)) = 10)) (PreH21 : ((Zlength (counters)) = 10)) (PreH22 : ((Zlength (mixed_output)) = 1000)) (PreH23 : (0 <= max_value)) (PreH24 : (max_value <= 999999999)) (PreH25 : (1 <= exponent)) (PreH26 : (exponent <= 100000000)) (PreH27 : (0 < (max_value ÷ exponent ))) (PreH28 : ((-1) <= i)) (PreH29 : (i < n_pre)) (PreH30 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH31 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10)))) (PreH32 : forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre)))) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre)))) (PreH34 : (PrefixMaximum input n_pre max_value )) (PreH35 : (DecimalExponent exponent )) (PreH36 : (RadixPassState input current exponent )) (PreH37 : (DigitHistogramPrefix current exponent n_pre histogram )) (PreH38 : (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output )) ,
  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 (replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) counters 0) - 1 )) (counters)) )
  **  (IntArray.mixed_full ( &( "output" ) ) 1000 mixed_output )
|--
  “ (0 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) - 1 )) (counters))) (0))) ” 
  &&  “ ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ((replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) - 1 )) (counters))) (0)) < 1000) ” 
  &&  “ (exponent <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (exponent >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (0 <= (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) ” 
  &&  “ ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10) ” 
  &&  “ (1 <= (Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) ” 
  &&  “ ((Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre) ” 
  &&  “ (max_value <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (max_value >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (histogram)) = 10) ” 
  &&  “ ((Zlength (counters)) = 10) ” 
  &&  “ ((Zlength (mixed_output)) = 1000) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ))) /\ ((((Znth (k_2) (current) (0)) ÷ exponent ) % ( 10 ) ) < 10))) ” 
  &&  “ forall (digit: Z) , (((0 <= digit) /\ (digit < 10)) -> ((((0 <= (Znth (digit) (histogram) (0))) /\ ((Znth (digit) (histogram) (0)) <= n_pre)) /\ (0 <= (Znth (digit) (counters) (0)))) /\ ((Znth (digit) (counters) (0)) <= n_pre))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 <= i)) -> ((1 <= (Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0))) /\ ((Znth ((((Znth (k_3) (current) (0)) ÷ exponent ) % ( 10 ) )) (counters) (0)) <= n_pre))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (DigitHistogramPrefix current exponent n_pre histogram ) ” 
  &&  “ (BucketPlacementProgress current exponent (i + 1 ) histogram counters mixed_output ) ”
  &&  (((( &( "output" ) ) + ((Znth (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) (replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) counters 0) - 1 )) (counters)) 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i ( &( "output" ) ) (Znth (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) (replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) counters 0) - 1 )) (counters)) 0) 0 1000 mixed_output )
  **  (IntArray.full a_pre n_pre current )
  **  (IntArray.full ( &( "count" ) ) 10 (replace_Znth ((((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) )) (((Znth (((Znth (i) (current) (0)) ÷ exponent ) % ( 10 ) ) counters 0) - 1 )) (counters)) )
.

Definition sort_partial_solve_wit_17 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (working: (@list Z)) (pass_output: (@list Z)) (bucket_starts: (@list Z)) (current: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output)) = n_pre)) (PreH8 : ((Zlength (working)) = n_pre)) (PreH9 : (0 <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : (0 < (max_value ÷ exponent ))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (pass_output) (0)))) /\ ((Znth (k_2) (pass_output) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (working) (0)))) /\ ((Znth (k_2) (working) (0)) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (StableDigitPass current pass_output exponent )) (PreH22 : (RadixCopyPrefix current pass_output working i )) ,
  (IntArray.full a_pre n_pre working )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (bucket_starts)) = 10) ” 
  &&  “ ((Zlength (pass_output)) = n_pre) ” 
  &&  “ ((Zlength (working)) = n_pre) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (pass_output) (0)))) /\ ((Znth (k_2) (pass_output) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (working) (0)))) /\ ((Znth (k_2) (working) (0)) <= 999999999))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (StableDigitPass current pass_output exponent ) ” 
  &&  “ (RadixCopyPrefix current pass_output working i ) ”
  &&  (((( &( "output" ) ) + (i * sizeof(INT)))) # Int  |-> (Znth (i - 0 ) pass_output 0))
  **  (IntArray.missing_i ( &( "output" ) ) i 0 n_pre pass_output )
  **  (IntArray.full a_pre n_pre working )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
.

Definition sort_partial_solve_wit_18 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (i: Z) (exponent: Z) (max_value: Z) (working: (@list Z)) (pass_output: (@list Z)) (bucket_starts: (@list Z)) (current: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (input)) = n_pre)) (PreH5 : ((Zlength (current)) = n_pre)) (PreH6 : ((Zlength (bucket_starts)) = 10)) (PreH7 : ((Zlength (pass_output)) = n_pre)) (PreH8 : ((Zlength (working)) = n_pre)) (PreH9 : (0 <= max_value)) (PreH10 : (max_value <= 999999999)) (PreH11 : (1 <= exponent)) (PreH12 : (exponent <= 100000000)) (PreH13 : (0 < (max_value ÷ exponent ))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (pass_output) (0)))) /\ ((Znth (k_2) (pass_output) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (working) (0)))) /\ ((Znth (k_2) (working) (0)) <= 999999999)))) (PreH18 : (PrefixMaximum input n_pre max_value )) (PreH19 : (DecimalExponent exponent )) (PreH20 : (RadixPassState input current exponent )) (PreH21 : (StableDigitPass current pass_output exponent )) (PreH22 : (RadixCopyPrefix current pass_output working i )) ,
  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.full a_pre n_pre working )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
|--
  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (current)) = n_pre) ” 
  &&  “ ((Zlength (bucket_starts)) = 10) ” 
  &&  “ ((Zlength (pass_output)) = n_pre) ” 
  &&  “ ((Zlength (working)) = n_pre) ” 
  &&  “ (0 <= max_value) ” 
  &&  “ (max_value <= 999999999) ” 
  &&  “ (1 <= exponent) ” 
  &&  “ (exponent <= 100000000) ” 
  &&  “ (0 < (max_value ÷ exponent )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) <= 999999999))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((0 <= (Znth (k_2) (current) (0))) /\ ((Znth (k_2) (current) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (pass_output) (0)))) /\ ((Znth (k_2) (pass_output) (0)) <= 999999999)) /\ (0 <= (Znth (k_2) (working) (0)))) /\ ((Znth (k_2) (working) (0)) <= 999999999))) ” 
  &&  “ (PrefixMaximum input n_pre max_value ) ” 
  &&  “ (DecimalExponent exponent ) ” 
  &&  “ (RadixPassState input current exponent ) ” 
  &&  “ (StableDigitPass current pass_output exponent ) ” 
  &&  “ (RadixCopyPrefix current pass_output working i ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i a_pre i 0 n_pre working )
  **  (IntArray.seg ( &( "output" ) ) 0 n_pre pass_output )
  **  (IntArray.full ( &( "count" ) ) 10 bucket_starts )
  **  (IntArray.undef_seg ( &( "output" ) ) n_pre 1000 )
.

Module Type VC_Correct.


Axiom proof_of_sort_safety_wit_1 : sort_safety_wit_1.
Axiom proof_of_sort_safety_wit_2 : sort_safety_wit_2.
Axiom proof_of_sort_safety_wit_3 : sort_safety_wit_3.
Axiom proof_of_sort_safety_wit_4 : sort_safety_wit_4.
Axiom proof_of_sort_safety_wit_5 : sort_safety_wit_5.
Axiom proof_of_sort_safety_wit_6 : sort_safety_wit_6.
Axiom proof_of_sort_safety_wit_7 : sort_safety_wit_7.
Axiom proof_of_sort_safety_wit_8 : sort_safety_wit_8.
Axiom proof_of_sort_safety_wit_9 : sort_safety_wit_9.
Axiom proof_of_sort_safety_wit_10 : sort_safety_wit_10.
Axiom proof_of_sort_safety_wit_11 : sort_safety_wit_11.
Axiom proof_of_sort_safety_wit_12 : sort_safety_wit_12.
Axiom proof_of_sort_safety_wit_13 : sort_safety_wit_13.
Axiom proof_of_sort_safety_wit_14 : sort_safety_wit_14.
Axiom proof_of_sort_safety_wit_15 : sort_safety_wit_15.
Axiom proof_of_sort_safety_wit_16 : sort_safety_wit_16.
Axiom proof_of_sort_safety_wit_17 : sort_safety_wit_17.
Axiom proof_of_sort_safety_wit_18 : sort_safety_wit_18.
Axiom proof_of_sort_safety_wit_19 : sort_safety_wit_19.
Axiom proof_of_sort_safety_wit_20 : sort_safety_wit_20.
Axiom proof_of_sort_safety_wit_21 : sort_safety_wit_21.
Axiom proof_of_sort_safety_wit_22 : sort_safety_wit_22.
Axiom proof_of_sort_safety_wit_23 : sort_safety_wit_23.
Axiom proof_of_sort_safety_wit_24 : sort_safety_wit_24.
Axiom proof_of_sort_safety_wit_25 : sort_safety_wit_25.
Axiom proof_of_sort_safety_wit_26 : sort_safety_wit_26.
Axiom proof_of_sort_safety_wit_27 : sort_safety_wit_27.
Axiom proof_of_sort_safety_wit_28 : sort_safety_wit_28.
Axiom proof_of_sort_safety_wit_29 : sort_safety_wit_29.
Axiom proof_of_sort_safety_wit_30 : sort_safety_wit_30.
Axiom proof_of_sort_safety_wit_31 : sort_safety_wit_31.
Axiom proof_of_sort_safety_wit_32 : sort_safety_wit_32.
Axiom proof_of_sort_safety_wit_33 : sort_safety_wit_33.
Axiom proof_of_sort_safety_wit_34 : sort_safety_wit_34.
Axiom proof_of_sort_safety_wit_35 : sort_safety_wit_35.
Axiom proof_of_sort_safety_wit_36 : sort_safety_wit_36.
Axiom proof_of_sort_entail_wit_1 : sort_entail_wit_1.
Axiom proof_of_sort_entail_wit_2_1 : sort_entail_wit_2_1.
Axiom proof_of_sort_entail_wit_2_2 : sort_entail_wit_2_2.
Axiom proof_of_sort_entail_wit_3 : sort_entail_wit_3.
Axiom proof_of_sort_entail_wit_4 : sort_entail_wit_4.
Axiom proof_of_sort_entail_wit_5 : sort_entail_wit_5.
Axiom proof_of_sort_entail_wit_6 : sort_entail_wit_6.
Axiom proof_of_sort_entail_wit_7 : sort_entail_wit_7.
Axiom proof_of_sort_entail_wit_8 : sort_entail_wit_8.
Axiom proof_of_sort_entail_wit_9 : sort_entail_wit_9.
Axiom proof_of_sort_entail_wit_10 : sort_entail_wit_10.
Axiom proof_of_sort_entail_wit_11 : sort_entail_wit_11.
Axiom proof_of_sort_entail_wit_12 : sort_entail_wit_12.
Axiom proof_of_sort_entail_wit_13 : sort_entail_wit_13.
Axiom proof_of_sort_entail_wit_14 : sort_entail_wit_14.
Axiom proof_of_sort_entail_wit_15 : sort_entail_wit_15.
Axiom proof_of_sort_entail_wit_16 : sort_entail_wit_16.
Axiom proof_of_sort_entail_wit_17 : sort_entail_wit_17.
Axiom proof_of_sort_entail_wit_18 : sort_entail_wit_18.
Axiom proof_of_sort_entail_wit_19 : sort_entail_wit_19.
Axiom proof_of_sort_entail_wit_20 : sort_entail_wit_20.
Axiom proof_of_sort_entail_wit_21 : sort_entail_wit_21.
Axiom proof_of_sort_entail_wit_22 : sort_entail_wit_22.
Axiom proof_of_sort_entail_wit_23 : sort_entail_wit_23.
Axiom proof_of_sort_return_wit_1 : sort_return_wit_1.
Axiom proof_of_sort_return_wit_2 : sort_return_wit_2.
Axiom proof_of_sort_partial_solve_wit_1 : sort_partial_solve_wit_1.
Axiom proof_of_sort_partial_solve_wit_2 : sort_partial_solve_wit_2.
Axiom proof_of_sort_partial_solve_wit_3 : sort_partial_solve_wit_3.
Axiom proof_of_sort_partial_solve_wit_4 : sort_partial_solve_wit_4.
Axiom proof_of_sort_partial_solve_wit_5 : sort_partial_solve_wit_5.
Axiom proof_of_sort_partial_solve_wit_6 : sort_partial_solve_wit_6.
Axiom proof_of_sort_partial_solve_wit_7 : sort_partial_solve_wit_7.
Axiom proof_of_sort_partial_solve_wit_8 : sort_partial_solve_wit_8.
Axiom proof_of_sort_partial_solve_wit_9 : sort_partial_solve_wit_9.
Axiom proof_of_sort_partial_solve_wit_10 : sort_partial_solve_wit_10.
Axiom proof_of_sort_partial_solve_wit_11 : sort_partial_solve_wit_11.
Axiom proof_of_sort_partial_solve_wit_12 : sort_partial_solve_wit_12.
Axiom proof_of_sort_partial_solve_wit_13 : sort_partial_solve_wit_13.
Axiom proof_of_sort_partial_solve_wit_14 : sort_partial_solve_wit_14.
Axiom proof_of_sort_partial_solve_wit_15 : sort_partial_solve_wit_15.
Axiom proof_of_sort_partial_solve_wit_16 : sort_partial_solve_wit_16.
Axiom proof_of_sort_partial_solve_wit_17 : sort_partial_solve_wit_17.
Axiom proof_of_sort_partial_solve_wit_18 : sort_partial_solve_wit_18.

End VC_Correct.
